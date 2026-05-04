# Logic Agents and Reasoning

A first-order logic (FOL) automated theorem prover built in Python, using **sequent calculus** (Gentzen-style LK rules) to prove theorems drawn from the [TPTP benchmark library](https://www.tptp.org/). The system parses TPTP-formatted problem files, constructs sequents from axioms and conjectures, and runs a breadth-first proof search with prioritised inference rules.

---

## Table of Contents

- [Overview](#overview)
- [Architecture](#architecture)
- [Project Structure](#project-structure)
- [Module Reference](#module-reference)
  - [sequent.py — Formula AST & Normalisation](#sequentpy--formula-ast--normalisation)
  - [parser.py — TPTP File Parser](#parserpy--tptp-file-parser)
  - [prover.py — Sequent Calculus Prover](#proverpy--sequent-calculus-prover)
  - [main.py — Test Campaign Runner](#mainpy--test-campaign-runner)
  - [Original_Algorithm.py — Reference Implementation](#original_algorithmpy--reference-implementation)
- [TPTP Benchmark Problems](#tptp-benchmark-problems)
- [How the Prover Works](#how-the-prover-works)
  - [Sequent Calculus Rules](#sequent-calculus-rules)
  - [Proof Search Strategy](#proof-search-strategy)
  - [Quantifier Handling](#quantifier-handling)
- [Getting Started](#getting-started)
  - [Prerequisites](#prerequisites)
  - [Installation](#installation)
  - [Running the Prover](#running-the-prover)
- [Output Format](#output-format)
- [Limitations](#limitations)
- [Contributing](#contributing)

---

## Overview

This project implements an **automated theorem prover** for first-order classical logic. Given a set of axioms and a conjecture encoded in the TPTP syntax, the prover attempts to derive a closed proof using the rules of the sequent calculus. Each proof obligation is presented as a *sequent* of the form:

```
Γ ⊢ Δ
```

where `Γ` is the list of premises (axioms/hypotheses) and `Δ` is the list of goals (conjectures). The prover succeeds if it can close every open branch of the proof tree, returning `True`. It returns `False` when it exhausts all possibilities, and `None` (timeout) when the search exceeds the configured time limit.

---

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                        main.py                          │
│   Campaign → FilesystemWalker → TestRunner → Reporter   │
└───────────────────────┬─────────────────────────────────┘
                        │ calls
┌───────────────────────▼─────────────────────────────────┐
│                       prover.py                         │
│   Run() → Parser → [Sequent] → Prover (BFS search)     │
└────────────┬──────────────────────────┬─────────────────┘
             │                          │
┌────────────▼──────────┐  ┌────────────▼────────────────┐
│       parser.py       │  │         sequent.py           │
│  Read TPTP files →    │  │  Formula AST nodes:          │
│  Tokenise → Build     │  │  Atom, And, Or, Implies,     │
│  Sequents             │  │  ForAll, Exists, Negation…   │
└───────────────────────┘  └─────────────────────────────┘
```

---

## Project Structure

```
Logic_Agents_And_Reasoning/
│
├── main.py                  # Test campaign orchestrator
├── prover.py                # Core sequent calculus prover
├── parser.py                # TPTP file reader, lexer, and sequent assembler
├── sequent.py               # First-order logic formula AST and normalisation
├── Original_Algorithm.py    # Reference/original version of the prover
│
└── TPTP/                    # 433 TPTP benchmark problem files (.p)
    ├── SYN*.p               # Syntactic benchmark problems
    ├── SYO*.p               # Additional syntactic/logical benchmarks
    └── SWB*.p               # Further benchmark problems
```

---

## Module Reference

### `sequent.py` — Formula AST & Normalisation

Defines the immutable formula node types that represent the abstract syntax tree (AST) of first-order logic formulas.

**Formula node types:**

| Class | Description | Example |
|---|---|---|
| `Atom(predicate, args)` | Atomic proposition or predicate | `p(x)`, `big_p` |
| `And(left, right)` | Conjunction | `A ∧ B` |
| `Or(left, right)` | Disjunction | `A ∨ B` |
| `Implies(left, right)` | Implication | `A ⇒ B` |
| `Iff(left, right)` | Biconditional | `A ⟺ B` |
| `Negation(predicate)` | Negation | `¬A` |
| `ForAll(variable, body)` | Universal quantifier | `∀x. A(x)` |
| `Exists(variable, body)` | Existential quantifier | `∃x. A(x)` |
| `Top()` | Logical truth | `⊤` |
| `Bottom()` | Logical falsehood | `⊥` |
| `Eq(left, right)` | Equality | `a = b` |
| `NEq(left, right)` | Inequality | `a ≠ b` |

The `Sequent` dataclass pairs a left-hand list of formulas (premises) with a right-hand list (conclusions).

**Normalisation** (`normalize`): Rewrites `Iff` into paired implications, and desugars `Eq`/`NEq` to `Atom("eq", ...)` and its negation, reducing the formula to a core calculus that the prover can handle uniformly.

**Formula building** (`Formula_Builder`): A recursive descent parser (`FormulaAssembler`) that converts a flat list of tokens into a nested formula tree, respecting operator precedence:

```
⟺  >  ⇒  >  ∨  >  ∧  >  ≠ / =
```

---

### `parser.py` — TPTP File Parser

Reads TPTP-formatted `.p` files and produces a list of `Sequent` objects ready for the prover.

**Three-stage pipeline:**

1. **Document processing** — `DocumentReader` / `DocumentCleaner`
   - Strips block (`/* … */`) and line (`% …`) comments.
   - Resolves `include()` directives by walking the directory tree.
   - Yields `AnnotatedFormula` records: `(dialect, identifier, role, expression)`.

2. **Lexical analysis** — `LexicalAnalyzer` / `Tokenise`
   - Converts a formula string into a flat list of tokens using compiled regex patterns.
   - Recognises keywords, connectives (`=>`, `<=>`, `~&`, `~|`), quantifier syntax (`![`, `?[`), atoms, variables, integers, and quoted strings.

3. **Sequent assembly** — `SequentBuilder` / `Parser`
   - Accumulates formulas classified as *axiom* roles (`axiom`, `hypothesis`, `assumption`, `lemma`, `theorem`, `corollary`, `plain`, `definition`) into the left-hand side.
   - Places `conjecture`-role formulas on the right-hand side.
   - Commits a sequent when a checkpoint heuristic fires (e.g., a `goal` identifier or a new axiom group starting with `a1`).
   - Supports the TPTP dialects: **FOF**, **TFF**, **THF**, **CNF**.

**Public interface:**
```python
from parser import Parser

sequents = Parser("TPTP/SYN058+1.p")
# Returns a list of Sequent objects
```

---

### `prover.py` — Sequent Calculus Prover

Implements the core BFS-based proof search over sequent calculus rules.

#### Key functions

| Function | Description |
|---|---|
| `Prover(sequent, max_depth)` | Main proof search loop; returns `True`, `False`, or `None` (exhausted) |
| `run_with_timeout(sequent, timeout)` | Runs `Prover` in a daemon thread with a wall-clock timeout |
| `Run(filepath, timeout)` | Parses a file and proves all sequents; returns `(results, pass_count)` |
| `Substitute(formula, variable, term)` | Capture-avoiding substitution throughout a formula tree |
| `Traverse_to_get_terms(seq)` | Collects ground terms from a sequent for quantifier instantiation |
| `rank_terms(terms, formula, seq)` | Heuristically orders candidate instantiation terms |

#### Inference rules implemented

**Propositional rules (priority 2 — deterministic, applied first):**

| Rule | Applied on | Effect |
|---|---|---|
| `not_right` | `¬A` on right | Move `A` to left |
| `not_left` | `¬A` on left | Move `A` to right |
| `and_left` | `A ∧ B` on left | Replace with `A`, `B` |
| `or_right` | `A ∨ B` on right | Replace with `A`, `B` |
| `implies_right` | `A ⇒ B` on right | Move `A` to left, keep `B` on right |

**Branching rules (priority 3 — create sub-goals):**

| Rule | Applied on | Effect |
|---|---|---|
| `and_right` | `A ∧ B` on right | Two branches: prove `A`, prove `B` |
| `or_left` | `A ∨ B` on left | Two branches: one with `A`, one with `B` |
| `implies_left` | `A ⇒ B` on left | Two branches: prove antecedent, add consequent |

**Quantifier rules (priority 4 — term instantiation):**

| Rule | Applied on | Effect |
|---|---|---|
| `for_all_right` | `∀x. A` on right | Introduce fresh variable `c`; replace with `A[c/x]` |
| `exists_left` | `∃x. A` on left | Introduce fresh constant `c`; replace with `A[c/x]` |
| `for_all_left` | `∀x. A` on left | Instantiate with a ground term from the sequent |
| `exists_right` | `∃x. A` on right | Instantiate with a ground term from the sequent |

**Axiom / closure rule (priority 1):**
- `id_rule`: closes a branch immediately if any atom appears on both sides, if `⊥` is on the left, or if `⊤` is on the right.

---

### `main.py` — Test Campaign Runner

Provides a high-level harness for running the prover over a directory of TPTP files and reporting aggregate statistics.

**Classes:**

| Class | Responsibility |
|---|---|
| `Campaign` | Orchestrates the full test run over a path |
| `FilesystemWalker` | Recursively discovers `.p` files under a given path |
| `TestRunner` | Calls `prover.Run()`, suppresses output, categorises results |
| `ReportBuilder` | Formats per-file status lines and the final summary |
| `Suite` | Accumulates aggregate statistics (files, sequents, pass/fail/timeout counts, duration) |
| `VerdictCount` | Per-file pass/fail/timeout tallies |

**Entry point:**
```python
# main.py — edit `path` to point at your file or directory
path = "problems_1000.p"
campaign = Campaign(path)
results = campaign.run()
ReportBuilder.summary(results, path)
```

---

### `Original_Algorithm.py` — Reference Implementation

Contains the original version of the prover before the refactor. It uses a tree-based `SearchNode` structure (`offspring`, `resolved`) and a `TermParser` helper with slightly different naming conventions. It serves as a reference baseline and illustrates the evolution of the design.

---

## TPTP Benchmark Problems

The `TPTP/` directory contains **433 benchmark problems** drawn from the [TPTP Problem Library](https://www.tptp.org/), a standard test suite for automated theorem proving systems. Problems are named using the TPTP naming convention:

- `SYN` — Syntactic problems (propositional and first-order logic identities)
- `SYO` — Syntactic/logical ordered problems
- `SWB` — Symmetry/structural problems

Each `.p` file is annotated with metadata including:
- **Domain** and **problem name** (e.g., *Pelletier Problem 28*)
- **Status** (`Theorem`, `CounterSatisfiable`, etc.)
- **Syntax statistics** (formula count, connective count, variable count)
- **SPC classification** (e.g., `FOF_THM_RFO_NEQ`)

Example problem header:
```prolog
% File   : SYN058+1 (Pelletier Problem 28)
% Status : Theorem
fof(pel28_1, axiom,    ![X] : (big_p(X) => ![Z] : big_q(Z))).
fof(pel28_2, axiom,    (![X] : (big_q(X) | big_r(X))) => ?[X1] : (big_q(X1) & big_s(X1))).
fof(pel28_3, axiom,    (?[X] : big_s(X)) => ![X1] : (big_f(X1) => big_g(X1))).
fof(pel28,   conjecture, ![X] : ((big_p(X) & big_f(X)) => big_g(X))).
```

---

## How the Prover Works

### Sequent Calculus Rules

The prover implements a subset of **Gentzen's LK calculus** for classical first-order logic. A sequent `Γ ⊢ Δ` is *valid* if every model satisfying all formulas in `Γ` also satisfies at least one formula in `Δ`. The proof rules decompose formulas until every branch is closed by the axiom rule.

### Proof Search Strategy

The search is a **BFS with a priority queue** implemented as a `deque` with `appendleft` for high-priority items:

1. **Priority 1 — Close immediately:** check `id_rule` before applying any rule.
2. **Priority 2 — Deterministic propositional rules:** applied greedily; each produces exactly one child sequent.
3. **Quantifier elimination (eigen-variable rules):** `for_all_right` and `exists_left` use fresh constants and are applied before branching.
4. **Priority 3 — Branching propositional rules:** `and_right`, `or_left`, `implies_left` each generate two sub-goals.
5. **Priority 4 — Term instantiation:** ground terms are collected from the sequent and ranked heuristically. Fresh variables are used as a last resort.

Duplicate formulas are removed at each step via `remove_duplicates` to avoid trivial loops.

### Quantifier Handling

Substitution (`Substitute`) is **capture-avoiding**: if a bound variable clashes with a substituted term, the bound variable is renamed to a fresh symbol before substitution proceeds. Ground terms are extracted from existing atoms in the sequent to guide instantiation, and `rank_terms` prefers terms that appear in atoms sharing a predicate name with the quantified formula's body.

---

## Getting Started

### Prerequisites

- Python **3.8** or later (uses `dataclasses`, `pathlib`, `threading`)
- No third-party packages required — the standard library is sufficient.

### Installation

```bash
git clone https://github.com/SamTruongG/Logic_Agents_And_Reasoning.git
cd Logic_Agents_And_Reasoning
```

### Running the Prover

**Prove all problems in the TPTP directory:**

Edit the `path` variable in `main.py`:

```python
# main.py
path = "TPTP"   # or point to a specific .p file
```

Then run:

```bash
python main.py
```

**Prove a single file directly from Python:**

```python
from prover import Run

results, pass_count = Run("TPTP/SYN058+1.p", timeout=30)
print(f"Passed {pass_count}/{len(results)} sequents")
```

**Use the prover programmatically:**

```python
from parser import Parser
from prover import run_with_timeout

sequents = Parser("TPTP/SYN058+1.p")
for seq in sequents:
    result = run_with_timeout(seq, timeout=10)
    if result is True:
        print("Proved:", seq)
    elif result is False:
        print("No proof found:", seq)
    else:
        print("Timed out:", seq)
```

---

## Output Format

**Per-file output** during a campaign run:

```
[1] SYN058+1.p: pass=1
[2] SYN059+1.p: pass=2 fail=1
[3] SYN060+1.p: timeout=1
```

**Summary printed at the end:**

```
=== Summary ===
Source:          TPTP
Files processed: 433
Sequents total:  512
  Passed:    498
  Failed:    8
  Timed out: 6
Total time:      142.35 s
```

Verdict meanings:

| Verdict | Meaning |
|---|---|
| `pass` | Proof found — sequent is a theorem |
| `fail` | Proof search exhausted — sequent is not provable (or requires deeper search) |
| `timeout` | Proof search exceeded the time limit (default: 30 s) |

---

## Limitations

- **No unification / resolution:** the prover uses ground-term instantiation rather than unification, so some theorems requiring non-trivial term construction may not be provable.
- **Completeness:** the BFS is complete for propositional logic, but the `max_depth` limit (default 500) and term-instantiation strategy mean that some valid FOL theorems may time out.
- **Equality:** `=` and `≠` are desugared to `Atom("eq", ...)` but no equality axioms (reflexivity, symmetry, transitivity, congruence) are built in — problems relying on equality reasoning will not be proved unless those axioms are present in the problem file itself.
- **Single-threaded search:** each proof runs in one thread; parallelism across sequents is not currently supported.
- **Supported dialects:** FOF, TFF, THF, CNF are parsed, but higher-order features in THF beyond what can be lowered to FOL are silently ignored.

---

## Contributing

Contributions are welcome. Areas that would benefit from improvement include:

- Adding a unification-based instantiation strategy (e.g., paramodulation or resolution).
- Implementing built-in equality reasoning.
- Extending the test suite with harder TPTP domains (e.g., arithmetic, set theory).
- Adding a CLI argument parser so the target path and timeout can be specified without editing source.
- Improving loop detection to avoid redundant sequents during quantifier instantiation.
