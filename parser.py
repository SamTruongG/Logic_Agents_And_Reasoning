"""TPTP file processor: from source to sequent list.

Consists of three independent subsystems:
    • Document reading: resolve includes, extract annotated formulas
    • Lexical analysis: convert formula strings to token streams
    • Sequent assembly: group formulas into axiom/conjecture pairs
"""

import os
import re
import warnings
from dataclasses import dataclass
from typing import Iterator, List, Set, Optional, Tuple
from enum import Enum

import formula_sequent
from formula_sequent import Sequent, Formula_Builder, normalize


# =============================================================================
# Constants and enumerations
# =============================================================================

class Dialect(Enum):
    """Supported TPTP logical dialects."""
    FOF = "fof"
    TFF = "tff"
    THF = "thf"
    CNF = "cnf"


class AxiomRole(Enum):
    """Roles that denote assumptions/premises."""
    AXIOM = "axiom"
    HYPOTHESIS = "hypothesis"
    ASSUMPTION = "assumption"
    LEMMA = "lemma"
    THEOREM = "theorem"
    COROLLARY = "corollary"
    PLAIN = "plain"
    DEFINITION = "definition"


@dataclass(frozen=True)
class AnnotatedFormula:
    """A single formula extracted from source."""
    dialect: str
    identifier: str
    role: str
    expression: str


# =============================================================================
# Document processing subsystem
# =============================================================================

class DocumentCleaner:
    """Removes comments from TPTP source."""
    
    _BLOCK = re.compile(r"/\*.*?\*/", re.DOTALL)
    _LINE = re.compile(r"%[^\n]*")
    
    @classmethod
    def sanitize(cls, source: str) -> str:
        """Strip block and line comments."""
        temp = cls._BLOCK.sub("", source)
        return cls._LINE.sub("", temp)


class StatementExtractor:
    """Splits cleaned source into top-level declarations."""
    
    def __init__(self, text: str):
        self.source = text
        self.position = 0
        self.length = len(text)
    
    def __iter__(self):
        """Yield each declaration terminated by '.'."""
        return self
    
    def __next__(self) -> str:
        """Extract next statement."""
        declaration = self._extract_next()
        if declaration is None:
            raise StopIteration
        return declaration
    
    def _extract_next(self) -> Optional[str]:
        """Read characters until finding a '.' at depth 0."""
        state = _ParserState()
        start = self.position
        
        while self.position < self.length:
            ch = self.source[self.position]
            
            if state.is_in_sq_string:
                if ch == "'" and not self._is_escaped(self.position):
                    state.is_in_sq_string = False
            elif state.is_in_dq_string:
                if ch == '"' and not self._is_escaped(self.position):
                    state.is_in_dq_string = False
            elif ch == "'":
                state.is_in_sq_string = True
            elif ch == '"':
                state.is_in_dq_string = True
            elif ch in "([":
                state.nesting += 1
            elif ch in ")]":
                state.nesting -= 1
            elif ch == "." and state.nesting == 0:
                if self._is_valid_terminator(self.position):
                    result = self.source[start:self.position].strip()
                    self.position += 1
                    if result:
                        return result
            
            self.position += 1
        
        tail = self.source[start:].strip()
        return tail if tail else None
    
    def _is_escaped(self, idx: int) -> bool:
        """Check if character at idx is escaped."""
        return idx > 0 and self.source[idx - 1] == "\\"
    
    def _is_valid_terminator(self, idx: int) -> bool:
        """Ensure '.' is not part of a decimal number."""
        prev = self.source[idx - 1] if idx > 0 else ""
        nxt = self.source[idx + 1] if idx + 1 < self.length else ""
        return not (prev.isdigit() and nxt.isdigit())


class BracketMatcher:
    """Utility for extracting content between matching brackets."""
    
    @staticmethod
    def extract_inner(text: str, open_pos: int) -> Optional[str]:
        """Return substring strictly between matched parens at open_pos."""
        depth = 0
        in_sq = in_dq = False
        
        for i in range(open_pos, len(text)):
            ch = text[i]
            
            if in_sq:
                if ch == "'" and text[i - 1] != "\\":
                    in_sq = False
                continue
            
            if in_dq:
                if ch == '"' and text[i - 1] != "\\":
                    in_dq = False
                continue
            
            if ch == "'":
                in_sq = True
            elif ch == '"':
                in_dq = True
            elif ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    return text[open_pos + 1:i]
        
        return None


class TextSplitter:
    """Splits text at delimiters while respecting nesting."""
    
    @staticmethod
    def split_at(text: str, delimiter: str, max_parts: Optional[int] = None) -> List[str]:
        """Split on delimiter at depth 0, respecting quotes."""
        parts = []
        current = []
        depth = 0
        in_sq = in_dq = False
        splits = 0
        
        for ch in text:
            if in_sq:
                current.append(ch)
                if ch == "'":
                    in_sq = False
                continue
            
            if in_dq:
                current.append(ch)
                if ch == '"':
                    in_dq = False
                continue
            
            if ch == "'":
                in_sq = True
                current.append(ch)
            elif ch == '"':
                in_dq = True
                current.append(ch)
            elif ch in "([":
                depth += 1
                current.append(ch)
            elif ch in ")]":
                depth -= 1
                current.append(ch)
            elif ch == delimiter and depth == 0 and (max_parts is None or splits < max_parts):
                parts.append("".join(current))
                current = []
                splits += 1
            else:
                current.append(ch)
        
        parts.append("".join(current))
        return parts


class IncludeResolver:
    """Locates TPTP include targets."""
    
    @staticmethod
    def resolve(target: str, referrer: str) -> Optional[str]:
        """Find include file relative to referrer."""
        base_dir = os.path.dirname(referrer)
        
        # Check relative to referrer
        direct = os.path.join(base_dir, target)
        if os.path.exists(direct):
            return os.path.abspath(direct)
        
        # Check in current working directory
        if os.path.exists(target):
            return os.path.abspath(target)
        
        # Search up the directory tree
        current = base_dir
        for _ in range(10):
            candidate = os.path.join(current, target)
            if os.path.exists(candidate):
                return os.path.abspath(candidate)
            parent = os.path.dirname(current)
            if parent == current:
                break
            current = parent
        
        return None


class DocumentReader:
    """Walks TPTP file hierarchy and yields annotated formulas."""
    
    def __init__(self, filepath: str):
        self.filepath = filepath
        self.visited: Set[str] = set()
    
    def read(self) -> Iterator[AnnotatedFormula]:
        """Yield all formulas from file and includes."""
        yield from self._traverse(os.path.abspath(self.filepath))
    
    def _traverse(self, path: str) -> Iterator[AnnotatedFormula]:
        """Recursively process file and its includes."""
        abs_path = os.path.abspath(path)
        
        if abs_path in self.visited:
            return
        
        self.visited.add(abs_path)
        
        with open(abs_path, "r") as handle:
            content = DocumentCleaner.sanitize(handle.read())
        
        for declaration in StatementExtractor(content):
            paren_pos = declaration.find("(")
            if paren_pos < 0:
                continue
            
            header = declaration[:paren_pos].strip().lower()
            
            if header == "include":
                self._handle_include(declaration, paren_pos, abs_path)
            elif header in ("fof", "tff", "thf", "cnf"):
                formula_obj = self._parse_declaration(header, declaration, paren_pos)
                if formula_obj:
                    yield formula_obj
    
    def _handle_include(self, declaration: str, paren_pos: int, current_path: str) -> None:
        """Process an include directive."""
        inner = BracketMatcher.extract_inner(declaration, paren_pos)
        if inner is None:
            return
        
        parts = TextSplitter.split_at(inner, ",", max_parts=1)
        target = parts[0].strip().strip("'\"")
        
        resolved_path = IncludeResolver.resolve(target, current_path)
        if resolved_path is None:
            warnings.warn(f"Include not resolved: {target!r} from {current_path}")
        else:
            yield from self._traverse(resolved_path)
    
    def _parse_declaration(self, dialect: str, declaration: str, paren_pos: int) -> Optional[AnnotatedFormula]:
        """Extract and validate formula annotation."""
        inner = BracketMatcher.extract_inner(declaration, paren_pos)
        if inner is None:
            return None
        
        fields = TextSplitter.split_at(inner, ",", max_parts=2)
        if len(fields) < 3:
            return None
        
        return AnnotatedFormula(
            dialect=dialect,
            identifier=fields[0].strip(),
            role=fields[1].strip(),
            expression=fields[2].strip()
        )


def Read_File(filepath: str) -> Iterator[Tuple[str, str, str, str]]:
    """Public interface: yield (dialect, name, role, formula_str)."""
    reader = DocumentReader(filepath)
    for formula in reader.read():
        yield formula.dialect, formula.identifier, formula.role, formula.expression


# =============================================================================
# Lexical analysis subsystem
# =============================================================================

_TOKEN_PATTERNS = [
    (r"%[^\n]*", None),                                      # Comment
    (r"\$[a-zA-Z_][a-zA-Z0-9_]*", "DEFINED"),              # $-prefixed
    (r"'(?:[^'\\]|\\.)*'", "QUOTED1"),                      # Single quotes
    (r'"(?:[^"\\]|\\.)*"', "QUOTED2"),                      # Double quotes
    (r"[+-]?\d+\.\d*(?:[eE][+-]?\d+)?|[+-]?\d+[eE][+-]?\d+", "REAL"),
    (r"[+-]?\d+", "INT"),
    (r"<=>", "IFF"),
    (r"<~>", "XOR"),
    (r"~&", "NAND"),
    (r"~\|", "NOR"),
    (r"=>", "IMPL"),
    (r"-->", "ARROW"),
    (r"<<", "SUBTYPE"),
    (r"<=", "RIMPL"),
    (r"!=", "NEQ"),
    (r"!\[", "FORALL_OPEN"),
    (r"\?\[", "EXISTS_OPEN"),
    (r"[~&|=^*+!?@,:()\[\]]", "PUNCT"),
    (r"[a-zA-Z_][a-zA-Z0-9_]*", "WORD"),
    (r"\s+", None),                                          # Whitespace
]

_COMPILED_PATTERNS = [(re.compile(pat), tok) for pat, tok in _TOKEN_PATTERNS]


class LexicalAnalyzer:
    """Converts formula strings into token streams."""
    
    @staticmethod
    def tokenize(formula: str) -> List[str]:
        """Extract tokens from formula, dropping comments and whitespace."""
        tokens = []
        idx = 0
        
        while idx < len(formula):
            matched = False
            
            for compiled_pattern, token_kind in _COMPILED_PATTERNS:
                match = compiled_pattern.match(formula, idx)
                if match:
                    if token_kind is not None:
                        tokens.append(match.group())
                    idx = match.end()
                    matched = True
                    break
            
            if not matched:
                idx += 1  # Skip unrecognized character
        
        return tokens


def Tokenise(formula: str) -> List[str]:
    """Public interface: tokenize formula string."""
    return LexicalAnalyzer.tokenize(formula)


# =============================================================================
# Sequent assembly subsystem
# =============================================================================

class _ParserState:
    """Tracks parsing state during document traversal."""
    
    def __init__(self):
        self.is_in_sq_string = False
        self.is_in_dq_string = False
        self.nesting = 0


class SequentAccumulator:
    """Collects formulas into axiom/conjecture groups."""
    
    def __init__(self):
        self.axioms: List = []
        self.conjecture = None
    
    def add_axiom(self, formula) -> None:
        """Append to axiom list."""
        self.axioms.append(formula)
    
    def set_conjecture(self, formula) -> None:
        """Set the conjecture (overwriting previous if any)."""
        self.conjecture = formula
    
    def build(self) -> Optional[Sequent]:
        """Create sequent if non-empty."""
        if self.axioms or self.conjecture is not None:
            right_side = [self.conjecture] if self.conjecture else []
            return Sequent(self.axioms, right_side)
        return None
    
    def reset(self) -> None:
        """Clear for next group."""
        self.axioms = []
        self.conjecture = None


class SequentBuilder:
    """Transforms annotated formulas into sequent list."""
    
    _AXIOM_ROLES = frozenset({
        "axiom", "hypothesis", "assumption",
        "lemma", "theorem", "corollary",
        "plain", "definition",
    })
    
    def __init__(self, filepath: str):
        self.filepath = filepath
        self.accumulator = SequentAccumulator()
        self.sequents: List[Sequent] = []
    
    def build(self) -> List[Sequent]:
        """Parse file and return all sequents."""
        for dialect, name, role, source in Read_File(self.filepath):
            formula = normalize(Formula_Builder(Tokenise(source)))
            
            if role.lower() in self._AXIOM_ROLES:
                self.accumulator.add_axiom(formula)
            elif role.lower() == "conjecture":
                self.accumulator.set_conjecture(formula)
            
            # Checkpoint: create sequent when heuristics trigger
            if self._should_checkpoint(name, role):
                self._commit()
                if role.lower() != "conjecture":
                    self.accumulator.add_axiom(formula)
        
        self._commit()
        return self.sequents
    
    def _should_checkpoint(self, name: str, role: str) -> bool:
        """Determine if we should finalize current group."""
        if name == "goal":
            return True
        
        return (
            self.accumulator.conjecture is not None
            and name.startswith("a1")
            and self.accumulator.axioms
        )
    
    def _commit(self) -> None:
        """Finalize current group and reset."""
        sequent = self.accumulator.build()
        if sequent:
            self.sequents.append(sequent)
        self.accumulator.reset()


def Parser(filepath: str, debug: bool = False) -> List[Sequent]:
    """Public interface: parse TPTP file to sequent list."""
    builder = SequentBuilder(filepath)
    return builder.build()
