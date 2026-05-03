"""First-order logic syntax tree and parsing.

Defines immutable formula nodes with a builder that consumes token sequences.
Public interface (class names, attributes) is preserved for compatibility.
"""

from dataclasses import dataclass
from typing import List, Optional, Tuple


# =============================================================================
# Formula node definitions (dataclass-based)
# =============================================================================

@dataclass(frozen=True)
class Formula:
    """Base marker for formula nodes."""
    pass


@dataclass(frozen=True)
class Atom(Formula):
    predicate: str
    args: List['Formula'] = None
    
    def __post_init__(self):
        if self.args is None:
            object.__setattr__(self, 'args', [])
    
    def __str__(self):
        if not self.args:
            return self.predicate
        arg_str = ", ".join(str(a) for a in self.args)
        return f"{self.predicate}({arg_str})"
    
    __repr__ = __str__


@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula
    
    def __str__(self):
        return f"({self.left} \\and {self.right})"
    __repr__ = __str__


@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula
    
    def __str__(self):
        return f"({self.left} \\or {self.right})"
    __repr__ = __str__


@dataclass(frozen=True)
class Implies(Formula):
    left: Formula
    right: Formula
    
    def __str__(self):
        return f"({self.left} => {self.right})"
    __repr__ = __str__


@dataclass(frozen=True)
class Iff(Formula):
    left: Formula
    right: Formula
    
    def __str__(self):
        return f"({self.left} <=> {self.right})"
    __repr__ = __str__


@dataclass(frozen=True)
class Eq(Formula):
    left: Formula
    right: Formula
    
    def __str__(self):
        return f"({self.left} = {self.right})"
    __repr__ = __str__


@dataclass(frozen=True)
class NEq(Formula):
    left: Formula
    right: Formula
    
    def __str__(self):
        return f"({self.left} != {self.right})"
    __repr__ = __str__


@dataclass(frozen=True)
class Negation(Formula):
    predicate: Formula
    
    def __str__(self):
        return f"~{self.predicate}"
    __repr__ = __str__


@dataclass(frozen=True)
class ForAll(Formula):
    variable: str
    body: Formula
    
    def __str__(self):
        return f"(∀{self.variable}: {self.body})"
    __repr__ = __str__


@dataclass(frozen=True)
class Exists(Formula):
    variable: str
    body: Formula
    
    def __str__(self):
        return f"(∃{self.variable}: {self.body})"
    __repr__ = __str__


@dataclass(frozen=True)
class Top(Formula):
    def __str__(self):
        return "⊤"
    __repr__ = __str__


@dataclass(frozen=True)
class Bottom(Formula):
    def __str__(self):
        return "⊥"
    __repr__ = __str__


@dataclass
class Sequent:
    left: List[Formula]
    right: List[Formula]
    
    def __str__(self):
        lhs = ", ".join(str(f) for f in self.left)
        rhs = ", ".join(str(f) for f in self.right)
        return f"{lhs} ⊢ {rhs}"
    
    __repr__ = __str__


# =============================================================================
# Token processing utilities
# =============================================================================

class TokenAnalyzer:
    """Utilities for examining token sequences."""
    
    @staticmethod
    def is_fully_parenthesized(tokens: List[str]) -> bool:
        """Check if opening paren at index 0 closes only at final position."""
        if not tokens or tokens[0] != "(" or tokens[-1] != ")":
            return False
        
        depth, final = 0, len(tokens) - 1
        for i, tok in enumerate(tokens):
            depth += (tok == "(") - (tok == ")")
            if depth == 0 and i < final:
                return False
        
        return True
    
    @staticmethod
    def partition_by_comma(tokens: List[str]) -> List[List[str]]:
        """Split token list at top-level commas."""
        groups, current, nesting = [], [], 0
        
        for tok in tokens:
            nesting += (tok == "(") - (tok == ")")
            
            if tok == "," and nesting == 0:
                if current:
                    groups.append(current)
                current = []
            else:
                current.append(tok)
        
        if current:
            groups.append(current)
        
        return groups
    
    @staticmethod
    def find_operator(tokens: List[str], op: str) -> int:
        """Locate first top-level occurrence of operator, or -1."""
        depth = 0
        for i, tok in enumerate(tokens):
            depth += (tok == "(") - (tok == ")")
            if depth == 0 and tok == op:
                return i
        return -1
    
    @staticmethod
    def extract_quantified_vars(tokens: List[str], start: int) -> Tuple[List[str], int]:
        """Extract variable list from quantifier syntax, return (vars, body_index)."""
        variables = []
        pos = start
        
        while tokens[pos] != "]":
            if tokens[pos] != ",":
                variables.append(tokens[pos])
            pos += 1
        
        return variables, pos + 2  # skip ']' and ':'


# =============================================================================
# Formula construction from token sequences
# =============================================================================

_OPERATOR_PRECEDENCE = [
    [("<=>", Iff)],
    [("=>", Implies)],
    [("|", Or)],
    [("&", And)],
    [("!=", NEq), ("=", Eq)],
]


class FormulaAssembler:
    """Recursive descent builder for formula syntax trees."""
    
    @classmethod
    def build(cls, tokens: List[str]) -> Formula:
        """Construct formula tree from token list."""
        return cls._parse_or_default(tokens)
    
    @classmethod
    def _parse_or_default(cls, tokens: List[str]) -> Formula:
        """Entry point with sensible defaults for edge cases."""
        if not tokens:
            return Top()
        
        if len(tokens) == 1:
            return cls._parse_singleton(tokens[0])
        
        if TokenAnalyzer.is_fully_parenthesized(tokens):
            return cls.build(tokens[1:-1])
        
        return cls._parse_complex(tokens)
    
    @classmethod
    def _parse_singleton(cls, token: str) -> Formula:
        """Handle single-token formulas."""
        if token == "$true":
            return Top()
        if token == "$false":
            return Bottom()
        return Atom(token, [])
    
    @classmethod
    def _parse_complex(cls, tokens: List[str]) -> Formula:
        """Handle multi-token formulas."""
        
        # Prefix operators
        if tokens[0] == "~":
            return Negation(cls.build(tokens[1:]))
        
        if tokens[0] == "![":
            vars, body_idx = TokenAnalyzer.extract_quantified_vars(tokens, 1)
            return cls._nest_quantifiers(ForAll, vars, cls.build(tokens[body_idx:]))
        
        if tokens[0] == "?[":
            vars, body_idx = TokenAnalyzer.extract_quantified_vars(tokens, 1)
            return cls._nest_quantifiers(Exists, vars, cls.build(tokens[body_idx:]))
        
        # Predicate / function application
        if cls._is_predicate_application(tokens):
            return cls._parse_predicate_app(tokens)
        
        # Binary operators (by precedence)
        for operators in _OPERATOR_PRECEDENCE:
            for op_symbol, op_class in operators:
                split_idx = TokenAnalyzer.find_operator(tokens, op_symbol)
                if split_idx >= 0:
                    return op_class(
                        cls.build(tokens[:split_idx]),
                        cls.build(tokens[split_idx + 1:])
                    )
        
        # Infix operators appearing mid-stream
        result = cls._parse_delayed_operator(tokens)
        if result:
            return result
        
        # Fallback
        return Atom(tokens[0], [cls.build(tokens)])
    
    @classmethod
    def _is_predicate_application(cls, tokens: List[str]) -> bool:
        """Check if tokens match 'name(...)' pattern."""
        if len(tokens) < 3 or tokens[1] != "(" or tokens[-1] != ")":
            return False
        
        depth = 0
        for j in range(1, len(tokens)):
            depth += (tokens[j] == "(") - (tokens[j] == ")")
            if depth == 0 and j < len(tokens) - 1:
                return False
        
        return True
    
    @classmethod
    def _parse_predicate_app(cls, tokens: List[str]) -> Atom:
        """Parse function/predicate application."""
        name = tokens[0]
        arg_tokens = tokens[2:-1]
        args = [cls.build(arg) for arg in TokenAnalyzer.partition_by_comma(arg_tokens)]
        return Atom(name, args)
    
    @classmethod
    def _parse_delayed_operator(cls, tokens: List[str]) -> Optional[Formula]:
        """Scan for operators appearing after initial position."""
        depth = 0
        
        for i, tok in enumerate(tokens):
            depth += (tok == "(") - (tok == ")")
            
            if depth == 0:
                if tok == "~":
                    return Negation(cls.build(tokens[i + 1:]))
                
                if tok == "![":
                    vars, body_idx = TokenAnalyzer.extract_quantified_vars(tokens, i + 1)
                    return cls._nest_quantifiers(ForAll, vars, cls.build(tokens[body_idx:]))
                
                if tok == "?[":
                    vars, body_idx = TokenAnalyzer.extract_quantified_vars(tokens, i + 1)
                    return cls._nest_quantifiers(Exists, vars, cls.build(tokens[body_idx:]))
        
        return None
    
    @staticmethod
    def _nest_quantifiers(quant_class, variables: List[str], body: Formula) -> Formula:
        """Layer quantifiers for multiple variables."""
        node = body
        for var in reversed(variables):
            node = quant_class(var, node)
        return node


def Formula_Builder(tokens: List[str]) -> Formula:
    """Public interface: build formula from token list."""
    return FormulaAssembler.build(tokens)


# =============================================================================
# Formula normalization
# =============================================================================

class FormulaNormalizer:
    """Reduces non-kernel operators to core calculus."""
    
    @classmethod
    def normalize(cls, node: Formula) -> Formula:
        """Rewrite formula to eliminate Iff, Eq, NEq."""
        
        if isinstance(node, Iff):
            left, right = cls.normalize(node.left), cls.normalize(node.right)
            return And(Implies(left, right), Implies(right, left))
        
        if isinstance(node, Eq):
            left, right = cls.normalize(node.left), cls.normalize(node.right)
            return Atom("eq", [left, right])
        
        if isinstance(node, NEq):
            left, right = cls.normalize(node.left), cls.normalize(node.right)
            return Negation(Atom("eq", [left, right]))
        
        # Recursive cases
        if isinstance(node, (And, Or, Implies)):
            return type(node)(cls.normalize(node.left), cls.normalize(node.right))
        
        if isinstance(node, Negation):
            return Negation(cls.normalize(node.predicate))
        
        if isinstance(node, (ForAll, Exists)):
            return type(node)(node.variable, cls.normalize(node.body))
        
        # Leaves
        return node


def normalize(node: Formula) -> Formula:
    """Public interface: normalize formula."""
    return FormulaNormalizer.normalize(node)
