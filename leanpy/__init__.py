"""
LeanPy: Lean 定理证明器核心逻辑的 Python 复刻。

这是一个简化但完整的 Lean-like 依赖类型理论实现，
展示了 Curry-Howard 同构、依赖类型和归纳构造演算的核心机制。
"""

__version__ = "0.1.0"

# 导出核心模块
from .name import Name, mk_name
from .level import Level, imax, level_of_nat
from .expr import (
    Expr, BinderInfo, Literal,
    arrow, forall_, lam, app
)

# 这些在运行时导入以避免循环依赖


def _load_full():
    from . import environment
    from . import inductive
    from . import reducer
    from . import typechecker
    from . import parser
    from . import tactic
    return environment, inductive, reducer, typechecker, parser, tactic


__all__ = [
    'Name', 'mk_name',
    'Level', 'imax', 'level_of_nat',
    'Expr', 'BinderInfo', 'Literal',
    'arrow', 'forall_', 'lam', 'app',
]
