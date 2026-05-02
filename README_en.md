# LeanPy

> A Python library for interacting with Lean theorem prover

## Project Overview

LeanPy is an experimental project aimed at exploring interaction between Lean 4 and Python, providing formal proof capabilities.

**Core Goals:**
- Implement Lean core type system in Python
- Provide a clean theorem proving interface
- Support formal mathematical reasoning

## Quick Start

```python
import leanpy

# Create expression
expr = leanpy.Expr("∀ n : Nat, n + 0 = n")

# Type checking
result = leanpy.type_check(expr)
print(result)
```

## Project Structure

```
leanpy/
├── leanpy/              # Core Code
│   ├── __init__.py      # Module Entry
│   ├── environment.py   # Environment Management
│   ├── expr.py          # Expression Representation
│   ├── inductive.py     # Inductive Types
│   ├── level.py         # Universe Levels
│   ├── name.py          # Name Management
│   ├── parser.py        # Parser
│   ├── reducer.py       # Reducer
│   ├── tactic.py        # Tactic System
│   ├── typechecker.py   # Type Checker
│   ├── examples.py      # Examples
│   └── test_core.py     # Core Tests
├── LEAN_EXPLAINED.md    # Lean Concept Explanation
├── lean_core_structure.md # Lean Core Structure Documentation
├── README.md            # Documentation (Chinese)
├── README_en.md         # Documentation (English)
└── LICENSE              # License
```

## Core Modules

| Module | Description |
|--------|-------------|
| `environment.py` | Lean environment management, maintaining definitions and theorems |
| `expr.py` | Expression data structures and operations |
| `inductive.py` | Inductive type definitions and handling |
| `level.py` | Universe level system |
| `name.py` | Name and namespace management |
| `parser.py` | Expression parsing |
| `reducer.py` | β-reduction and δ-reduction |
| `tactic.py` | Proof tactics |
| `typechecker.py` | Type checking and inference |

## Installation

```bash
# Clone repository
git clone https://github.com/hctj353056/leanpy.git
cd leanpy

# Install dependencies
pip install -e .

# Optional: Install Lean 4 (via elan)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

## Dependencies

- Python >= 3.10
- Lean 4 (via elan) - Optional

## Version History

| Version | Date | Changes |
|---------|------|---------|
| v1.0 | - | Initial version, core type system implemented |

## Author

FuYou ♡

## License

MIT License

---

*FuShangGe · LeanPy Project*
