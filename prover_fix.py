import parser
import formula_sequent
import threading
from collections import deque



fresh_counter = 0
def fresh_var():
    global fresh_counter
    fresh_counter += 1
    return f"fresh_{fresh_counter}"


def parse_term_args(s):
    args = []
    current = []
    depth = 0
    for ch in s:
        if ch == ',' and depth == 0:
            args.append(''.join(current).strip())
            current = []
        else:
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            current.append(ch)
    if current:
        args.append(''.join(current).strip())
    return args


def parse_predicate_args(pred_string):
    cached = parse_cache.get(pred_string)
    if cached is not None:
        return cached
    idx = pred_string.find('(')
    if idx == -1:
        result = pred_string, []
    else:
        name = pred_string[:idx]
        inner = pred_string[idx + 1:-1]
        result = (name, parse_term_args(inner) if inner.strip() else [])
    parse_cache[pred_string] = result
    return result

parse_cache: dict = {}


def rebuild_atom(name, args):
    if not args:
        return name
    return f"{name}({','.join(args)})"


def remove_duplicates(formulas):
    seen, out = set(), []
    for f in formulas:
        k = str(f)
        if k not in seen:
            seen.add(k)
            out.append(f)
    return out


def substitute_in_term(term, variable, replacement):
    if term == variable:
        return replacement
    fname, fargs = parse_predicate_args(term)
    if not fargs:
        return term
    new_args = [substitute_in_term(a, variable, replacement) for a in fargs]
    return rebuild_atom(fname, new_args)


def Substitute(formula, variable, term):
    if isinstance(formula, formula_sequent.Atom):
        pred, args = parse_predicate_args(formula.predicate)
        new_args = [substitute_in_term(a, variable, term) for a in args]
        return formula_sequent.Atom(rebuild_atom(pred, new_args))
    elif isinstance(formula, formula_sequent.And):
        return formula_sequent.And(Substitute(formula.left, variable, term),
                                   Substitute(formula.right, variable, term))
    elif isinstance(formula, formula_sequent.Or):
        return formula_sequent.Or(Substitute(formula.left, variable, term),
                                  Substitute(formula.right, variable, term))
    elif isinstance(formula, formula_sequent.Implies):
        return formula_sequent.Implies(Substitute(formula.left, variable, term),
                                       Substitute(formula.right, variable, term))
    elif isinstance(formula, formula_sequent.Negation):
        return formula_sequent.Negation(Substitute(formula.predicate, variable, term))
    elif isinstance(formula, formula_sequent.ForAll):
        if formula.variable == variable:
            return formula
        if formula.variable in term:
            new_bound = fresh_var()
            renamed_body = Substitute(formula.body, formula.variable,formula_sequent.Atom(new_bound).predicate)
            return formula_sequent.ForAll(new_bound,Substitute(renamed_body, variable, term))
        return formula_sequent.ForAll(formula.variable,
                                      Substitute(formula.body, variable, term))
    elif isinstance(formula, formula_sequent.Exists):
        if formula.variable == variable:
            return formula
        if formula.variable in term:
            new_bound = fresh_var()
            renamed_body = Substitute(formula.body, formula.variable,formula_sequent.Atom(new_bound).predicate)
            return formula_sequent.Exists(new_bound,Substitute(renamed_body, variable, term))
        return formula_sequent.Exists(formula.variable,Substitute(formula.body, variable, term))

    else:
        return formula



def Traverse_to_get_terms(seq):
    terms = set()
    def collect(formula):
        if isinstance(formula, formula_sequent.Atom):
            pred, args = parse_predicate_args(formula.predicate)
            for arg in args:
                # Collect only ground terms (start with lowercase or contain '(').
                # Variables are uppercase; we skip those.
                if arg and (arg[0].islower() or '(' in arg):
                    terms.add(arg)

        elif isinstance(formula, formula_sequent.And):
            collect(formula.left)
            collect(formula.right)
        elif isinstance(formula, formula_sequent.Or):
            collect(formula.left)
            collect(formula.right)
        elif isinstance(formula, formula_sequent.Implies):
            collect(formula.left)
            collect(formula.right)
        elif isinstance(formula, formula_sequent.Negation):
            collect(formula.predicate)
        elif isinstance(formula, formula_sequent.ForAll):
            collect(formula.body)
        elif isinstance(formula, formula_sequent.Exists):
            collect(formula.body)

    for f in seq.left + seq.right:
        collect(f)

    return terms if terms else {'default'}



def all_closed(node):
    if not node.children:
        return node.is_closed
    return all(all_closed(child) for child in node.children)


def id_rule(seq):
    right_atoms = {f.predicate for f in seq.right
                   if isinstance(f, formula_sequent.Atom)}
    for f in seq.left:
        if isinstance(f, formula_sequent.Bottom):
            return True
        if isinstance(f, formula_sequent.Atom) and f.predicate in right_atoms:
            return True
    for f in seq.right:
        if isinstance(f, formula_sequent.Top):
            return True
    return False


def not_right(seq):
    for i, formula in enumerate(seq.right):
        if isinstance(formula, formula_sequent.Negation):
            new_l = seq.left + [formula.predicate]
            new_r = seq.right[:i] + seq.right[i+1:]
            return formula_sequent.Sequent(new_l, new_r)
    return None

def not_left(seq):
    for i, formula in enumerate(seq.left):
        if isinstance(formula, formula_sequent.Negation):

            new_r = seq.right + [formula.predicate]
            new_l = seq.left[:i] + seq.left[i+1:]
            return formula_sequent.Sequent(new_l, new_r)
    return None

def and_left(seq):
    for i, formula in enumerate(seq.left):
        if isinstance(formula, formula_sequent.And):
            new_l = seq.left[:i] + [formula.left, formula.right] + seq.left[i+1:]
            return formula_sequent.Sequent(new_l, seq.right)
    return None

def and_right(seq):
    for i, formula in enumerate(seq.right):
        if isinstance(formula, formula_sequent.And):
            new_r = seq.right[:i] + [formula.left, formula.right] + seq.right[i+1:]
            return formula_sequent.Sequent(seq.left, new_r)
    return None

def or_right(seq):
    for i, formula in enumerate(seq.right):
        if isinstance(formula, formula_sequent.Or):
            new_r = seq.right[:i] + [formula.left, formula.right] + seq.right[i+1:]
            return formula_sequent.Sequent(seq.left, new_r)
    return None

def or_left(seq):
    for i, formula in enumerate(seq.left):
        if isinstance(formula, formula_sequent.Or):
            new_l_1 = seq.left[:i] + [formula.left] + seq.left[i+1:]
            new_l_2 = seq.left[:i] + [formula.right] + seq.left[i+1:]
            return formula_sequent.Sequent(new_l_1, seq.right), formula_sequent.Sequent(new_l_2, seq.right)
    return None

def implies_left(seq):
    for i, formula in enumerate(seq.left):
        if isinstance(formula, formula_sequent.Implies):
            new_l_1 = seq.left[:i] + seq.left[i+1:]
            new_r_1 = seq.right + [formula.left]
            new_l_2 = seq.left[:i] + [formula.right] + seq.left[i+1:]
            return formula_sequent.Sequent(new_l_1, new_r_1), formula_sequent.Sequent(new_l_2, seq.right)
    return None

def implies_right(seq):
    for i, formula in enumerate(seq.right):
        if isinstance(formula, formula_sequent.Implies):
            new_l = seq.left + [formula.left]
            new_r = seq.right[:i] + [formula.right] + seq.right[i+1:]
            return formula_sequent.Sequent(new_l, new_r)
    return None

def for_all_left(seq, term):
    for i, formula in enumerate(seq.left):
        if isinstance(formula, formula_sequent.ForAll):
            sub = Substitute(formula.body, formula.variable, term)
            # Keep the ∀ so it can be used again, add instantiation alongside it
            new_left = seq.left[:i] + [sub] + seq.left[i+1:]
            return formula_sequent.Sequent(new_left, seq.right)
    return None

def for_all_right(seq):
    for i, f in enumerate(seq.right):
        if isinstance(f, formula_sequent.ForAll):
            c = fresh_var()
            return formula_sequent.Sequent(
                seq.left,
                seq.right[:i] + [Substitute(f.body, f.variable, c)] + seq.right[i+1:]
            )
    return None

def exists_left(seq):
    for i, f in enumerate(seq.left):
        if isinstance(f, formula_sequent.Exists):
            c = fresh_var()
            return formula_sequent.Sequent(
                seq.left[:i] + [Substitute(f.body, f.variable, c)] + seq.left[i+1:],
                seq.right
            )
    return None

def exists_right(seq, term):
    for i, formula in enumerate(seq.right):
        if isinstance(formula, formula_sequent.Exists):
            sub = Substitute(formula.body, formula.variable, term)
            new_right = seq.right[:i] + [sub] + seq.right[i+1:]
            return formula_sequent.Sequent(seq.left, new_right)
    return None

def has_quantifier(formulas, qtype) -> bool:
    return any(isinstance(f, qtype) for f in formulas)


def rank_terms(terms, formula, seq):
    body = formula.body
    while isinstance(body, (formula_sequent.ForAll, formula_sequent.Exists)):
        body = body.body
    if isinstance(body, formula_sequent.Negation):
        body = body.predicate
    if not isinstance(body, formula_sequent.Atom):
        return list(terms)

    target, _ = parse_predicate_args(body.predicate)
    preferred = set()
    for f in seq.left + seq.right:
        if isinstance(f, formula_sequent.Atom):
            name, args = parse_predicate_args(f.predicate)
            if name == target:
                preferred.update(a for a in args if a in terms)

    return list(preferred & terms) + list(terms - preferred)


class ProofNode:
    __slots__ = ('seq', 'depth', 'used_terms')

    def __init__(self, seq, depth=0, used_terms=None):
        self.seq = seq
        self.depth = depth
        self.used_terms: set = used_terms if used_terms is not None else set()


def Prover(sequent, max_depth: int = 500):
    todo: deque[ProofNode] = deque([ProofNode(sequent)])
    seen = set()
    while todo:

        branch = todo.popleft()
        seq = branch.seq
        d = branch.depth

        if d > max_depth:
            return

        # priority 1
        if id_rule(seq):
            continue
        applied = False
        # priority 2
        for rule in [and_left, or_right, implies_right, not_left, not_right]:
            result = rule(seq)
            if result is not None:
                todo.appendleft(ProofNode(result, d+1, branch.used_terms.copy()))
                applied = True
                break
        if applied:
            continue



        if has_quantifier(seq.right, formula_sequent.ForAll):
            result = for_all_right(seq)
            if result:
                todo.appendleft(ProofNode(result, d + 1, branch.used_terms.copy()))
                continue
        if has_quantifier(seq.left, formula_sequent.Exists):
            result = exists_left(seq)
            if result:
                todo.appendleft(ProofNode(result, d + 1, branch.used_terms.copy()))
                continue


        # Priority 3
        result = and_left(seq)
        if result:
            todo.appendleft(ProofNode(
                formula_sequent.Sequent(remove_duplicates(result.left), result.right),
                d + 1, branch.used_terms.copy()))
            continue
        result = and_right(seq)
        if result:
            todo.appendleft(ProofNode(
                formula_sequent.Sequent(remove_duplicates(result.left), result.right),
                d + 1, branch.used_terms.copy()))
            continue
        for rule in [or_left, implies_left]:
            result = rule(seq)
            if result is not None:
                left_seq, right_seq = result
                # Both sub-goals must be proved; push both
                todo.appendleft(ProofNode(right_seq, d + 1, branch.used_terms.copy()))
                todo.appendleft(ProofNode(left_seq, d + 1, branch.used_terms.copy()))
                applied = True
                break
        if applied:
             continue

        # Priority 4
        terms = Traverse_to_get_terms(seq)
        unused = terms - branch.used_terms
        q_applied = False

        for rule, formulas, formula_type in [(for_all_left, seq.left, formula_sequent.ForAll),
                                             (exists_right, seq.right, formula_sequent.Exists)]:
            if not has_quantifier(formulas, formula_type):
                continue
            for formula in formulas:
                if not isinstance(formula, formula_type):
                    continue
                for term in rank_terms(unused if unused else terms, formula, seq):
                    result = rule(seq, term)
                    if result:
                        new_used = branch.used_terms | {term}
                        child_seq = formula_sequent.Sequent(
                            remove_duplicates(result.left), remove_duplicates(result.right))
                        child = ProofNode(child_seq, d + 1, new_used)
                        todo.appendleft(child)
                        q_applied = True
                        break
                if q_applied:
                    break
            if q_applied:
                break

        for rule, formulas, formula_type in (
                (for_all_left, seq.left, formula_sequent.ForAll),
                (exists_right, seq.right, formula_sequent.Exists),
        ):
            if has_quantifier(formulas, formula_type):
                fv = fresh_var()
                result = rule(seq, fv)
                if result:
                    todo.appendleft(ProofNode(result, d + 1, branch.used_terms.copy()))
                    q_applied = True
                    break
        if q_applied:
            continue


        return False

    return True



def run_with_timeout(sequent, timeout=30):
    result = [None]
    def target():
        result[0] = Prover(sequent)
    t = threading.Thread(target=target, daemon=True)
    t.start()
    t.join(timeout)
    return result[0]

def Run(filepath, timeout=30):
    sequents = parser.Parser(filepath)
    results = []
    count = 0

    for sequent in sequents:
        print(sequent)
        ok = run_with_timeout(sequent, timeout)
        if ok is None:
            print("Timed out")
        results.append(ok)
        if ok:
            count += 1
        print("Result:", ok)

    return results, count



