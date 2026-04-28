"""
宇宙层级（Universe Levels）系统。

Lean 使用 universe levels 来管理类型层级，避免 Girard 悖论。
每个类型都生活在一个 universe 中，而 universe 本身通过 Level 表达式描述。
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Optional, Set, Union


@dataclass(frozen=True)
class Level:
    """
    宇宙层级表达式。
    
    Level 的语法：
      ℓ ::= 0                     -- 零层级（对应 Prop/Sort 0）
          | u                     -- 层级变量
          | ℓ + n                 -- 后继层级（n 是自然数）
          | max(ℓ₁, ℓ₂)           -- 最大层级
          | imax(ℓ₁, ℓ₂)          -- 有条件的最大层级
    
    其中 imax(u, v) = 0 如果 v = 0，否则 = max(u, v)
    这保证了如果 codomain 在 Prop 中，则整个 Π-type 也在 Prop 中。
    """
    
    @dataclass(frozen=True)
    class Zero:
        """零层级"""
        def __repr__(self): return "0"
    
    @dataclass(frozen=True)
    class Succ:
        """后继层级 ℓ + 1"""
        level: 'Level'
        def __repr__(self): return f"({self.level} + 1)"
    
    @dataclass(frozen=True)
    class Max:
        """最大层级 max(ℓ₁, ℓ₂)"""
        lhs: 'Level'
        rhs: 'Level'
        def __repr__(self): return f"max({self.lhs}, {self.rhs})"
    
    @dataclass(frozen=True)
    class IMax:
        """有条件的最大层级 imax(ℓ₁, ℓ₂)"""
        lhs: 'Level'
        rhs: 'Level'
        def __repr__(self): return f"imax({self.lhs}, {self.rhs})"
    
    @dataclass(frozen=True)
    class Param:
        """层级变量（universe parameter）"""
        name: str
        def __repr__(self): return self.name
    
    @dataclass(frozen=True)
    class MSSucc:
        """多元后继：level + n"""
        level: 'Level'
        offset: int
        def __repr__(self):
            if self.offset == 0:
                return repr(self.level)
            return f"({self.level} + {self.offset})"

    # 单例：零层级
    ZERO = Zero()
    
    # Union type for matching
    kind: Union[Zero, Succ, Max, IMax, Param, MSSucc]
    
    def __init__(self, kind=None):
        if kind is None:
            object.__setattr__(self, 'kind', Level.ZERO)
        else:
            object.__setattr__(self, 'kind', kind)
    
    @staticmethod
    def zero() -> Level:
        """创建零层级"""
        return Level(Level.ZERO)
    
    @staticmethod
    def succ(l: Level) -> Level:
        """创建后继层级"""
        if isinstance(l.kind, Level.MSSucc):
            return Level(Level.MSSucc(l.kind.level, l.kind.offset + 1))
        return Level(Level.Succ(l))
    
    @staticmethod
    def max_level(l1: Level, l2: Level) -> Level:
        """创建最大层级"""
        # 简化：如果其中一个为零，返回另一个
        if isinstance(l1.kind, Level.Zero):
            return l2
        if isinstance(l2.kind, Level.Zero):
            return l1
        if l1 == l2:
            return l1
        return Level(Level.Max(l1, l2))
    
    @staticmethod
    def imax_level(l1: Level, l2: Level) -> Level:
        """创建有条件的最大层级"""
        # imax(u, 0) = 0
        if isinstance(l2.kind, Level.Zero):
            return Level.zero()
        # imax(u, v) = max(u, v) when v ≠ 0
        return Level.max_level(l1, l2)
    
    @staticmethod
    def param(name: str) -> Level:
        """创建层级变量"""
        return Level(Level.Param(name))
    
    def __repr__(self) -> str:
        return repr(self.kind)
    
    def __str__(self) -> str:
        return repr(self)
    
    def __eq__(self, other) -> bool:
        if not isinstance(other, Level):
            return False
        return self.kind == other.kind
    
    def __hash__(self) -> int:
        return hash(repr(self.kind))
    
    def is_zero(self) -> bool:
        """检查是否为零层级"""
        return isinstance(self.kind, Level.Zero)
    
    def is_param(self) -> bool:
        """检查是否是变量"""
        return isinstance(self.kind, Level.Param)
    
    def get_param_names(self) -> Set[str]:
        """获取所有层级变量名"""
        match self.kind:
            case Level.Param(name):
                return {name}
            case Level.Succ(level):
                return level.get_param_names()
            case Level.Max(lhs, rhs) | Level.IMax(lhs, rhs):
                return lhs.get_param_names() | rhs.get_param_names()
            case Level.MSSucc(level, _):
                return level.get_param_names()
            case _:
                return set()
    
    def subst(self, subst_map: dict) -> Level:
        """替换层级变量"""
        match self.kind:
            case Level.Param(name):
                return subst_map.get(name, self)
            case Level.Succ(level):
                return Level.succ(level.subst(subst_map))
            case Level.Max(lhs, rhs):
                return Level.max_level(lhs.subst(subst_map), rhs.subst(subst_map))
            case Level.IMax(lhs, rhs):
                return Level.imax_level(lhs.subst(subst_map), rhs.subst(subst_map))
            case Level.MSSucc(level, offset):
                new_level = level.subst(subst_map)
                if isinstance(new_level.kind, Level.MSSucc):
                    return Level(Level.MSSucc(new_level.kind.level, new_level.kind.offset + offset))
                result = new_level
                for _ in range(offset):
                    result = Level.succ(result)
                return result
            case _:
                return self


# 常用层级
Level.PROP = Level.zero()           # Sort 0 = Prop
Level.TYPE_0 = Level.succ(Level.PROP)  # Sort 1 = Type 0
Level.TYPE_1 = Level.succ(Level.TYPE_0)  # Sort 2 = Type 1


def imax(u: Level, v: Level) -> Level:
    """计算 imax(u, v)"""
    return Level.imax_level(u, v)


def level_of_nat(n: int) -> Level:
    """从自然数创建层级"""
    result = Level.zero()
    for _ in range(n):
        result = Level.succ(result)
    return result
