import parser
import formula_sequent
import copy
import threading
from pathlib import Path
from typing import List, Tuple, Dict, Set, Optional, Callable, Any, NamedTuple
import json
from datetime import datetime
import time


# =============================================================================
# DATA STRUCTURES
# =============================================================================

class SearchNode:
    """Represents a single state in the proof search tree."""
    __slots__ = ['sequent', 'offspring', 'resolved']
    
    def __init__(self, sequent):
        self.sequent = sequent
        self.offspring = []
        self.resolved = False


class TimeRecord(NamedTuple):
    """Timing data for a single proof attempt."""
    duration: float
    status: str


# =============================================================================
# SYMBOL & EXPRESSION MANIPULATION
# =============================================================================

_fresh_index = 0

def allocate_fresh() -> str:
    """Create unique symbol names."""
    global _fresh_index
    _fresh_index += 1
    return f"v{_fresh_index}"


class TermParser:
    """Handles parsing and manipulation of terms."""
    
    @staticmethod
    def split_args(s: str) -> List[str]:
        """Parse comma-separated arguments respecting nesting."""
        tokens, current, nesting = [], [], 0
        for char in s:
            if char == ',' and nesting == 0:
                tokens.append(''.join(current).strip())
                current = []
            else:
                nesting += (char == '(') - (char == ')')
                current.append(char)
        return tokens + ([''.join(current).strip()] if current else [])
    
    @staticmethod
    def decompose(expr: str) -> Tuple[str, List[str]]:
        """Extract functor and arguments."""
        idx = expr.find('(')
        if idx < 0:
            return expr, []
        return expr[:idx], TermParser.split_args(expr[idx+1:-1])
    
    @staticmethod
    def reconstruct(functor: str, args: List[str]) -> str:
        """Rebuild expression from functor and arguments."""
        return functor if not args else f"{functor}({','.join(args)})"
    
    @staticmethod
    def substitute(expr: str, var: str, replacement: str) -> str:
        """Replace variable with term in expression."""
        if expr == var:
            return replacement
        fn, params = TermParser.decompose(expr)
        if not params:
            return expr
        return TermParser.reconstruct(fn, [TermParser.substitute(p, var, replacement) for p in params])


class FormulaTransformer:
    """Applies substitutions across formula structures."""
    
    @staticmethod
    def apply(form, var: str, term: str):
        """Substitute all occurrences of variable in formula."""
        if isinstance(form, formula_sequent.Atom):
            fn, args = TermParser.decompose(form.predicate)
            return formula_sequent.Atom(TermParser.reconstruct(fn, 
                [TermParser.substitute(a, var, term) for a in args]))
        
        elif isinstance(form, (formula_sequent.And, formula_sequent.Or, formula_sequent.Implies)):
            return type(form)(
                FormulaTransformer.apply(form.left, var, term),
                FormulaTransformer.apply(form.right, var, term)
            )
        
        elif isinstance(form, formula_sequent.Negation):
            return formula_sequent.Negation(FormulaTransformer.apply(form.predicate, var, term))
        
        elif isinstance(form, formula_sequent.ForAll):
            if form.variable == var:
                return form
            if form.variable in term:
                fresh = allocate_fresh()
                body = FormulaTransformer.apply(form.body, form.variable, fresh)
                return formula_sequent.ForAll(fresh, FormulaTransformer.apply(body, var, term))
            return formula_sequent.ForAll(form.variable, FormulaTransformer.apply(form.body, var, term))
        
        elif isinstance(form, formula_sequent.Exists):
            if form.variable == var:
                return form
            if form.variable in term:
                fresh = allocate_fresh()
                body = FormulaTransformer.apply(form.body, form.variable, fresh)
                return formula_sequent.Exists(fresh, FormulaTransformer.apply(body, var, term))
            return formula_sequent.Exists(form.variable, FormulaTransformer.apply(form.body, var, term))
        
        return form


# =============================================================================
# SEQUENT ANALYSIS
# =============================================================================

class SequentInspector:
    """Extract information from sequents."""
    
    @staticmethod
    def is_closed(seq) -> bool:
        """Check closure conditions."""
        # Matching atoms
        for lf in seq.left:
            for rf in seq.right:
                if isinstance(lf, formula_sequent.Atom) and isinstance(rf, formula_sequent.Atom):
                    if lf.predicate == rf.predicate:
                        return True
        
        # Bottom on left or Top on right
        if any(isinstance(f, formula_sequent.Bottom) for f in seq.left):
            return True
        if any(isinstance(f, formula_sequent.Top) for f in seq.right):
            return True
        
        return False
    
    @staticmethod
    def extract_terms(seq) -> Set[str]:
        """Gather instantiable terms from sequent."""
        found = set()
        
        def harvest(f):
            if isinstance(f, formula_sequent.Atom):
                _, args = TermParser.decompose(f.predicate)
                for a in args:
                    if a and (a[0].islower() or '(' in a):
                        found.add(a)
            elif isinstance(f, (formula_sequent.And, formula_sequent.Or, formula_sequent.Implies)):
                harvest(f.left)
                harvest(f.right)
            elif isinstance(f, formula_sequent.Negation):
                harvest(f.predicate)
            elif isinstance(f, (formula_sequent.ForAll, formula_sequent.Exists)):
                harvest(f.body)
        
        for formula in seq.left + seq.right:
            harvest(formula)
        
        return found if found else {'default'}


# =============================================================================
# INFERENCE RULES
# =============================================================================

class Rule:
    """Base class for inference rules."""
    
    def trigger(self, seq) -> Optional[Any]:
        raise NotImplementedError
    
    def name(self) -> str:
        return self.__class__.__name__


class IdentityRule(Rule):
    def trigger(self, seq) -> bool:
        return SequentInspector.is_closed(seq)


class NegationRightRule(Rule):
    def trigger(self, seq):
        for i, f in enumerate(seq.right):
            if isinstance(f, formula_sequent.Negation):
                return formula_sequent.Sequent(seq.left + [f.predicate], seq.right[:i] + seq.right[i+1:])
        return None


class NegationLeftRule(Rule):
    def trigger(self, seq):
        for i, f in enumerate(seq.left):
            if isinstance(f, formula_sequent.Negation):
                return formula_sequent.Sequent(seq.left[:i] + seq.left[i+1:], seq.right + [f.predicate])
        return None


class ConjunctionLeftRule(Rule):
    def trigger(self, seq):
        for i, f in enumerate(seq.left):
            if isinstance(f, formula_sequent.And):
                return formula_sequent.Sequent(seq.left[:i] + [f.left, f.right] + seq.left[i+1:], seq.right)
        return None


class ConjunctionRightRule(Rule):
    def trigger(self, seq):
        for i, f in enumerate(seq.right):
            if isinstance(f, formula_sequent.And):
                return (formula_sequent.Sequent(seq.left, seq.right[:i] + [f.left] + seq.right[i+1:]),
                        formula_sequent.Sequent(seq.left, seq.right[:i] + [f.right] + seq.right[i+1:]))
        return None


class DisjunctionRightRule(Rule):
    def trigger(self, seq):
        for i, f in enumerate(seq.right):
            if isinstance(f, formula_sequent.Or):
                return formula_sequent.Sequent(seq.left, seq.right[:i] + [f.left, f.right] + seq.right[i+1:])
        return None


class DisjunctionLeftRule(Rule):
    def trigger(self, seq):
        for i, f in enumerate(seq.left):
            if isinstance(f, formula_sequent.Or):
                return (formula_sequent.Sequent(seq.left[:i] + [f.left] + seq.left[i+1:], seq.right),
                        formula_sequent.Sequent(seq.left[:i] + [f.right] + seq.left[i+1:], seq.right))
        return None


class ImplicationRightRule(Rule):
    def trigger(self, seq):
        for i, f in enumerate(seq.right):
            if isinstance(f, formula_sequent.Implies):
                return formula_sequent.Sequent(seq.left + [f.left], seq.right[:i] + [f.right] + seq.right[i+1:])
        return None


class ImplicationLeftRule(Rule):
    def trigger(self, seq):
        for i, f in enumerate(seq.left):
            if isinstance(f, formula_sequent.Implies):
                return (formula_sequent.Sequent(seq.left[:i] + seq.left[i+1:], seq.right + [f.left]),
                        formula_sequent.Sequent(seq.left[:i] + [f.right] + seq.left[i+1:], seq.right))
        return None


class UniversalRightRule(Rule):
    def trigger(self, seq):
        for i, f in enumerate(seq.right):
            if isinstance(f, formula_sequent.ForAll):
                c = allocate_fresh()
                return formula_sequent.Sequent(seq.left, seq.right[:i] + [FormulaTransformer.apply(f.body, f.variable, c)] + seq.right[i+1:])
        return None


class ExistentialLeftRule(Rule):
    def trigger(self, seq):
        for i, f in enumerate(seq.left):
            if isinstance(f, formula_sequent.Exists):
                c = allocate_fresh()
                return formula_sequent.Sequent(seq.left[:i] + [FormulaTransformer.apply(f.body, f.variable, c)] + seq.left[i+1:], seq.right)
        return None


class UniversalLeftRule(Rule):
    def __init__(self, t: str = None):
        self.term = t
    
    def trigger(self, seq):
        for i, f in enumerate(seq.left):
            if isinstance(f, formula_sequent.ForAll):
                sub = FormulaTransformer.apply(f.body, f.variable, self.term)
                return formula_sequent.Sequent(seq.left[:i] + [sub] + seq.left[i+1:], seq.right)
        return None


class ExistentialRightRule(Rule):
    def __init__(self, t: str = None):
        self.term = t
    
    def trigger(self, seq):
        for i, f in enumerate(seq.right):
            if isinstance(f, formula_sequent.Exists):
                sub = FormulaTransformer.apply(f.body, f.variable, self.term)
                return formula_sequent.Sequent(seq.left, seq.right[:i] + [sub] + seq.right[i+1:])
        return None


# =============================================================================
# PROOF SEARCH ENGINE
# =============================================================================

class ProofSearch:
    """Orchestrates proof search with rule priorities."""
    
    RULE_LAYERS = [
        [IdentityRule()],
        [ConjunctionLeftRule(), DisjunctionRightRule(), ImplicationRightRule(), 
         NegationLeftRule(), NegationRightRule()],
        [UniversalRightRule(), ExistentialLeftRule()],
        [ConjunctionRightRule(), DisjunctionLeftRule(), ImplicationLeftRule()],
    ]
    
    def __init__(self, sequent, max_depth: int = 1000):
        self.root = SearchNode(sequent)
        self.frontier = [self.root]
        self.depths = {id(self.root): 0}
        self.max_depth = max_depth
        self.history = {}
    
    def _check_identity(self, node) -> bool:
        return SequentInspector.is_closed(node.sequent)
    
    def _is_branching(self, rule) -> bool:
        return isinstance(rule, (ConjunctionRightRule, DisjunctionLeftRule, ImplicationLeftRule))
    
    def _create_child(self, result) -> SearchNode:
        return SearchNode(copy.deepcopy(result))
    
    def _create_children(self, result) -> Tuple[SearchNode, SearchNode]:
        left, right = result
        return SearchNode(copy.deepcopy(left)), SearchNode(copy.deepcopy(right))
    
    def _expand(self, node) -> bool:
        """Apply rules and return whether expansion occurred."""
        depth_val = self.depths[id(node)]
        if depth_val > self.max_depth:
            return False
        
        # Layer 1: Identity
        if self._check_identity(node):
            node.resolved = True
            return True
        
        # Layers 2-4: Inference rules
        for layer in self.RULE_LAYERS[1:]:
            for rule in layer:
                result = rule.trigger(node.sequent)
                if result is None:
                    continue
                
                if self._is_branching(rule):
                    left_child, right_child = self._create_children(result)
                    new_depth = depth_val + 1
                    self.depths[id(left_child)] = new_depth
                    self.depths[id(right_child)] = new_depth
                    node.offspring.extend([left_child, right_child])
                    self.frontier.extend([left_child, right_child])
                else:
                    child = self._create_child(result)
                    new_depth = depth_val + 1
                    self.depths[id(child)] = new_depth
                    node.offspring.append(child)
                    self.frontier.append(child)
                
                return True
        
        # Layer 5: Quantifier instantiation
        terms = SequentInspector.extract_terms(node.sequent)
        node_key = id(node)
        
        if node_key not in self.history:
            self.history[node_key] = {}
        
        for rule_class in [UniversalLeftRule, ExistentialRightRule]:
            for f in (node.sequent.left if rule_class == UniversalLeftRule else node.sequent.right):
                target_type = formula_sequent.ForAll if rule_class == UniversalLeftRule else formula_sequent.Exists
                if not isinstance(f, target_type):
                    continue
                
                f_key = id(f)
                if f_key not in self.history[node_key]:
                    self.history[node_key][f_key] = set()
                
                unused = terms - self.history[node_key][f_key]
                if unused:
                    for term in unused:
                        rule = rule_class(term)
                        result = rule.trigger(node.sequent)
                        if result:
                            child = SearchNode(result)
                            new_depth = depth_val + 1
                            self.depths[id(child)] = new_depth
                            node.offspring.append(child)
                            self.frontier.append(child)
                            self.history[node_key][f_key].add(term)
                            return True
        
        # Layer 5b: Fresh variable instantiation
        for rule_class in [UniversalLeftRule, ExistentialRightRule]:
            for f in (node.sequent.left if rule_class == UniversalLeftRule else node.sequent.right):
                target_type = formula_sequent.ForAll if rule_class == UniversalLeftRule else formula_sequent.Exists
                if isinstance(f, target_type):
                    rule = rule_class(allocate_fresh())
                    result = rule.trigger(node.sequent)
                    if result:
                        child = SearchNode(result)
                        new_depth = depth_val + 1
                        self.depths[id(child)] = new_depth
                        node.offspring.append(child)
                        self.frontier.append(child)
                        return True
        
        return False
    
    def _all_branches_resolved(self, node) -> bool:
        """Check if entire subtree is closed."""
        if not node.offspring:
            return node.resolved
        return all(self._all_branches_resolved(child) for child in node.offspring)
    
    def execute(self) -> bool:
        """Run complete search."""
        while self.frontier:
            node = self.frontier.pop(0)
            self._expand(node)
        
        return self._all_branches_resolved(self.root)


def prove(sequent, max_depth: int = 1000) -> bool:
    """Execute proof search on sequent."""
    search = ProofSearch(sequent, max_depth)
    return search.execute()


# =============================================================================
# EXECUTION & TIMING
# =============================================================================

def execute_with_limit(sequent, time_limit: int = 30) -> Tuple[Optional[bool], float]:
    """Run proof with wall-clock timeout."""
    outcome = [None]
    elapsed = [0]
    
    def worker():
        start = time.time()
        outcome[0] = prove(sequent)
        elapsed[0] = time.time() - start
    
    thread = threading.Thread(target=worker, daemon=True)
    start = time.time()
    thread.start()
    thread.join(time_limit)
    
    if thread.is_alive():
        elapsed[0] = time_limit
    
    return outcome[0], elapsed[0]


def humanize_duration(sec: float) -> str:
    """Format duration readably."""
    if sec < 1:
        return f"{sec*1000:.1f}ms"
    if sec < 60:
        return f"{sec:.2f}s"
    if sec < 3600:
        m, s = int(sec // 60), int(sec % 60)
        return f"{m}m {s}s"
    h, m, s = int(sec // 3600), int((sec % 3600) // 60), int(sec % 60)
    return f"{h}h {m}m {s}s"


# =============================================================================
# BATCH PROCESSING
# =============================================================================

def digest_file(path: str, limit: int = 30, loud: bool = True) -> Dict:
    """Process single problem file."""
    tick = time.time()
    
    if loud:
        print(f"\n{'='*70}\nFile: {Path(path).name}\n{'='*70}")
    
    try:
        sequences = parser.Parser(path)
    except Exception as e:
        if loud:
            print(f"Parse error: {e}")
        return {
            'name': Path(path).name, 'ok': False, 'why': str(e),
            'wins': 0, 'total': 0, 'secs': time.time() - tick
        }
    
    verdicts, times = [], []
    wins = 0
    
    for idx, seq in enumerate(sequences, 1):
        if loud:
            print(f"[{idx}] {seq}", end=" ")
        
        try:
            res, dur = execute_with_limit(seq, limit)
            times.append(dur)
            
            if res is True:
                wins += 1
                badge = "✓"
            elif res is False:
                badge = "✗"
            else:
                badge = "⏱"
            
            verdicts.append(res)
            if loud:
                print(f"→ {badge} {humanize_duration(dur)}")
        except Exception as e:
            if loud:
                print(f"→ ERROR: {e}")
            verdicts.append(None)
    
    return {
        'name': Path(path).name, 'ok': True,
        'wins': wins, 'total': len(verdicts),
        'ratio': 100*wins/len(verdicts) if verdicts else 0,
        'times': times, 'proof_secs': sum(times),
        'secs': time.time() - tick
    }


def digest_folder(dir_path: str, limit: int = 30, loud: bool = True, store: bool = True) -> Dict:
    """Process all files in folder."""
    overall_tick = time.time()
    base = Path(dir_path)
    
    if not base.exists():
        print(f"Not found: {dir_path}")
        return {}
    
    files = sorted(base.glob("*.p"))
    if not files:
        print(f"No .p files: {dir_path}")
        return {}
    
    print(f"\nFound {len(files)} files | Limit: {limit}s | Start: {datetime.now().strftime('%H:%M:%S')}")
    
    outcomes = {}
    total_wins, total_tasks = 0, 0
    total_proof_secs = 0
    
    for pfile in files:
        try:
            res = digest_file(str(pfile), limit, loud)
            outcomes[pfile.name] = res
            
            if res['ok']:
                total_wins += res['wins']
                total_tasks += res['total']
                total_proof_secs += res['proof_secs']
        except Exception as e:
            print(f"Error: {pfile.name}: {e}")
            outcomes[pfile.name] = {'name': pfile.name, 'ok': False, 'why': str(e), 'secs': 0}
    
    overall_secs = time.time() - overall_tick
    
    print(f"\n{'='*70}\nRESULTS\n{'='*70}")
    print(f"Files: {len(files)} | Success: {sum(1 for r in outcomes.values() if r['ok'])} | Failed: {sum(1 for r in outcomes.values() if not r['ok'])}")
    print(f"Tasks: {total_tasks} | Proved: {total_wins} | Rate: {100*total_wins/total_tasks if total_tasks else 0:.1f}%")
    
    print(f"\n{'='*70}\nTIMING\n{'='*70}")
    print(f"Proof time: {humanize_duration(total_proof_secs)} | Total: {humanize_duration(overall_secs)}")
    if total_tasks:
        print(f"Avg/task: {humanize_duration(total_proof_secs/total_tasks)}")
    
    print(f"\n{'='*70}\nPER-FILE\n{'='*70}")
    print(f"{'Name':<40} {'Score':<12} {'Rate':<8} {'Time'}")
    print(f"{'-'*70}")
    
    for fname in sorted(outcomes.keys()):
        rec = outcomes[fname]
        if rec['ok']:
            print(f"{fname:<40} {rec['wins']:3}/{rec['total']:<6} {rec['ratio']:5.1f}% {humanize_duration(rec['secs']):>12}")
        else:
            print(f"{fname:<40} FAIL: {rec['why']}")
    
    if store:
        out_file = base / "result.json"
        report = {
            'ts': datetime.now().isoformat(),
            'dir': str(base),
            'count': len(files),
            'success': sum(1 for r in outcomes.values() if r['ok']),
            'tasks': total_tasks,
            'wins': total_wins,
            'rate': 100*total_wins/total_tasks if total_tasks else 0,
            'proof_secs': total_proof_secs,
            'total_secs': overall_secs,
            'data': outcomes
        }
        
        try:
            with open(out_file, 'w') as f:
                json.dump(report, f, indent=2)
            print(f"\nSaved: {out_file}")
        except Exception as e:
            print(f"Save error: {e}")
    
    return outcomes


# =============================================================================
# ENTRY POINT
# =============================================================================

if __name__ == "__main__":
    CONFIG = {
        'folder': 'TPTP_Problems',
        'timeout': 30,
        'verbose': True,
        'save': True
    }
    
    digest_folder(CONFIG['folder'], CONFIG['timeout'], CONFIG['verbose'], CONFIG['save'])


