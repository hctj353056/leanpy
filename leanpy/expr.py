"""
Lean 核心表达式 AST（抽象语法树）。

这是 Lean 类型系统的心脏。所有项（term）、类型（type）、命题（proposition）
都统一为 Expr。这是 Curry-Howard 同构的核心体现。

Expr 的设计基于 de Bruijn 索引，避免 α-转换问题。
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Optional, Union, Tuple
from enum import Enum, auto

from .name import Name
from .level import Level


class BinderInfo(Enum):
    """
    绑定器信息，描述 λ/Π 绑定变量的行为。
    
    - DEFAULT: 普通绑定（显式参数）
    - IMPLICIT: 隐式参数 {x : A}
    - STRICT_IMPLICT: 严格隐式参数 ⦃x : A⦄
    - INST_IMPLICIT: 实例隐式参数 [x : A]（类型类实例）
    """
    DEFAULT = auto()
    IMPLICIT = auto()
    STRICT_IMPLICIT = auto()
    INST_IMPLICIT = auto()


class Literal:
    """字面量：自然数或字符串"""
    
    @dataclass(frozen=True)
    class NatVal:
        val: int
    
    @dataclass(frozen=True)
    class StrVal:
        val: str


@dataclass(frozen=True)
class Expr:
    """
    Lean 核心表达式。
    
    这是 Curry-Howard 同构的载体：命题即类型，证明即程序。
    所有表达式统一使用此类型表示。
    
    Expr 的语法（核心层）：
      e ::= bvar idx                 -- 绑定变量（de Bruijn 索引）
          | fvar id                  -- 自由变量（局部常量引用）
          | mvar id                  -- 元变量（待填充的"洞"）
          | sort u                   -- 宇宙层级（Sort u）
          | const name levels        -- 全局常量引用
          | app fn arg               -- 函数应用
          | lam name type body bi    -- λ 抽象（函数引入）
          | forallE name type body bi -- Π 类型（依赖函数类型）
          | letE name type value body -- let 绑定
          | lit literal              -- 字面量
    
    de Bruijn 索引规则：
    - λ x : A. body 中，x 在 body 中被表示为 bvar 0
    - body 中原来引用外层第 n 个绑定的变量变为 bvar (n+1)
    - 例如：λ x. λ y. x 表示为 lam(A, lam(B, bvar 1))
    """
    
    # ===== 构造函数 =====
    
    @dataclass(frozen=True)
    class BVar:
        """绑定变量：de Bruijn 索引"""
        idx: int  # 0 = 最近绑定，1 = 外层第1个，...
    
    @dataclass(frozen=True)
    class FVar:
        """自由变量：局部常量引用（唯一 ID）"""
        id: int   # 唯一标识符
    
    @dataclass(frozen=True)
    class MVar:
        """元变量：待填充的"洞"（metavariable）"""
        id: int   # 唯一标识符
    
    @dataclass(frozen=True)
    class Sort:
        """宇宙层级：Sort u"""
        level: Level
        
        def __repr__(self):
            if self.level == Level.PROP:
                return "Prop"
            elif self.level == Level.TYPE_0:
                return "Type"
            else:
                return f"Sort {self.level}"
    
    @dataclass(frozen=True)
    class Const:
        """全局常量引用"""
        name: Name
        levels: List[Level]  # universe 实例化参数
    
    @dataclass(frozen=True)
    class App:
        """函数应用：fn arg"""
        fn: 'Expr'
        arg: 'Expr'
    
    @dataclass(frozen=True)
    class Lam:
        """λ 抽象：λ (name : type). body"""
        name: str           # 绑定变量名（用于显示）
        dtype: 'Expr'       # 绑定变量类型
        body: 'Expr'       # 函数体（内部使用 de Bruijn 索引）
        binder_info: BinderInfo = BinderInfo.DEFAULT
    
    @dataclass(frozen=True)
    class ForallE:
        """Π 类型 / 依赖函数类型：Π (name : type). body"""
        name: str           # 绑定变量名
        dtype: 'Expr'       # 绑定变量类型
        body: 'Expr'        # 结果类型（可依赖 name）
        binder_info: BinderInfo = BinderInfo.DEFAULT
    
    @dataclass(frozen=True)
    class LetE:
        """let 绑定：let name : type := value in body"""
        name: str           # 变量名
        dtype: 'Expr'       # 变量类型
        value: 'Expr'       # 绑定值
        body: 'Expr'        # 作用域体
    
    @dataclass(frozen=True)
    class Lit:
        """字面量"""
        literal: Union[Literal.NatVal, Literal.StrVal]
    
    @dataclass(frozen=True)
    class Proj:
        """投影：结构体字段访问"""
        type_name: Name
        field_idx: int
        struct: 'Expr'
    
    # ===== 构造函数结束 =====
    
    kind: Union[BVar, FVar, MVar, Sort, Const, App, Lam, ForallE, LetE, Lit, Proj]
    
    def __init__(self, kind):
        object.__setattr__(self, 'kind', kind)
    
    # ===== 便捷构造方法 =====
    
    @staticmethod
    def bvar(idx: int) -> Expr:
        """创建绑定变量"""
        return Expr(Expr.BVar(idx))
    
    @staticmethod
    def fvar(id: int) -> Expr:
        """创建自由变量"""
        return Expr(Expr.FVar(id))
    
    @staticmethod
    def mvar(id: int) -> Expr:
        """创建元变量"""
        return Expr(Expr.MVar(id))
    
    @staticmethod
    def sort(level: Level) -> Expr:
        """创建宇宙层级表达式"""
        return Expr(Expr.Sort(level))
    
    @staticmethod
    def const(name: Name, levels: List[Level] = None) -> Expr:
        """创建全局常量引用"""
        return Expr(Expr.Const(name, levels or []))
    
    @staticmethod
    def app(fn: Expr, arg: Expr) -> Expr:
        """创建函数应用"""
        return Expr(Expr.App(fn, arg))
    
    @staticmethod
    def lam(name: str, dtype: Expr, body: Expr, binder_info: BinderInfo = BinderInfo.DEFAULT) -> Expr:
        """创建 λ 抽象"""
        return Expr(Expr.Lam(name, dtype, body, binder_info))
    
    @staticmethod
    def forallE(name: str, dtype: Expr, body: Expr, binder_info: BinderInfo = BinderInfo.DEFAULT) -> Expr:
        """创建 Π 类型"""
        return Expr(Expr.ForallE(name, dtype, body, binder_info))
    
    @staticmethod
    def letE(name: str, dtype: Expr, value: Expr, body: Expr) -> Expr:
        """创建 let 绑定"""
        return Expr(Expr.LetE(name, dtype, value, body))
    
    @staticmethod
    def lit_nat(n: int) -> Expr:
        """创建自然数字面量"""
        return Expr(Expr.Lit(Literal.NatVal(n)))
    
    @staticmethod
    def lit_str(s: str) -> Expr:
        """创建字符串字面量"""
        return Expr(Expr.Lit(Literal.StrVal(s)))
    
    # ===== 多参数应用 =====
    
    @staticmethod
    def mk_app(fn: Expr, args: List[Expr]) -> Expr:
        """创建多参数应用：(((fn arg1) arg2) ... argN)"""
        result = fn
        for arg in args:
            result = Expr.app(result, arg)
        return result
    
    @staticmethod
    def mk_lam(names_dtypes: List[Tuple[str, Expr]], body: Expr) -> Expr:
        """创建多参数 λ：λ x1 : A1. λ x2 : A2. ... body"""
        result = body
        for name, dtype in reversed(names_dtypes):
            result = Expr.lam(name, dtype, result)
        return result
    
    @staticmethod
    def mk_forallE(names_dtypes: List[Tuple[str, Expr]], body: Expr) -> Expr:
        """创建多参数 Π：Π x1 : A1. Π x2 : A2. ... body"""
        result = body
        for name, dtype in reversed(names_dtypes):
            result = Expr.forallE(name, dtype, result)
        return result
    
    @staticmethod
    def mk_arrow(src: Expr, dst: Expr) -> Expr:
        """创建非依赖函数类型：src → dst（即 Π _:src. dst）"""
        return Expr.forallE("_", src, dst)
    
    # ===== 属性方法 =====
    
    def is_bvar(self) -> bool:
        return isinstance(self.kind, Expr.BVar)
    
    def is_fvar(self) -> bool:
        return isinstance(self.kind, Expr.FVar)
    
    def is_mvar(self) -> bool:
        return isinstance(self.kind, Expr.MVar)
    
    def is_sort(self) -> bool:
        return isinstance(self.kind, Expr.Sort)
    
    def is_const(self) -> bool:
        return isinstance(self.kind, Expr.Const)
    
    def is_app(self) -> bool:
        return isinstance(self.kind, Expr.App)
    
    def is_lam(self) -> bool:
        return isinstance(self.kind, Expr.Lam)
    
    def is_forallE(self) -> bool:
        return isinstance(self.kind, Expr.ForallE)
    
    def is_letE(self) -> bool:
        return isinstance(self.kind, Expr.LetE)
    
    def is_arrow(self) -> bool:
        """检查是否是非依赖函数类型（伪箭头）"""
        return self.is_forallE() and self.kind.body.is_bvar() and self.kind.body.kind.idx == 0
    
    def get_app_fn(self) -> Expr:
        """获取应用链的函数头"""
        e = self
        while e.is_app():
            e = e.kind.fn
        return e
    
    def get_app_args(self) -> List[Expr]:
        """获取应用链的所有参数"""
        args = []
        e = self
        while e.is_app():
            args.append(e.kind.arg)
            e = e.kind.fn
        return list(reversed(args))
    
    def __repr__(self) -> str:
        """简洁表示"""
        return self._repr_impl(0)
    
    def _repr_impl(self, depth: int) -> str:
        if depth > 10:
            return "..."
        
        match self.kind:
            case Expr.BVar(idx):
                return f"#{idx}"
            case Expr.FVar(id):
                return f"fv{id}"
            case Expr.MVar(id):
                return f"?{id}"
            case Expr.Sort(level):
                if level == Level.PROP:
                    return "Prop"
                elif level == Level.TYPE_0:
                    return "Type"
                else:
                    return f"Sort({level})"
            case Expr.Const(name, levels):
                if levels:
                    return f"{name}.{{{','.join(str(l) for l in levels)}}}"
                return str(name)
            case Expr.App(fn, arg):
                return f"({fn._repr_impl(depth+1)} {arg._repr_impl(depth+1)})"
            case Expr.Lam(name, dtype, body, bi):
                bi_mark = ""
                if bi == BinderInfo.IMPLICIT:
                    bi_mark = "{"
                elif bi == BinderInfo.STRICT_IMPLICIT:
                    bi_mark = "⦃"
                return f"(λ {bi_mark}{name} : {dtype._repr_impl(depth+1)}. {body._repr_impl(depth+1)})"
            case Expr.ForallE(name, dtype, body, bi):
                # 检查是否是非依赖箭头
                if body.is_bvar() and body.kind.idx == 0 and bi == BinderInfo.DEFAULT:
                    return f"({dtype._repr_impl(depth+1)} → ...)"
                return f"(Π {name} : {dtype._repr_impl(depth+1)}. {body._repr_impl(depth+1)})"
            case Expr.LetE(name, dtype, value, body):
                return f"(let {name} : {dtype._repr_impl(depth+1)} := {value._repr_impl(depth+1)} in {body._repr_impl(depth+1)})"
            case Expr.Lit(Literal.NatVal(val)):
                return str(val)
            case Expr.Lit(Literal.StrVal(val)):
                return f'"{val}"'
            case Expr.Proj(_, idx, struct):
                return f"{struct._repr_impl(depth+1)}.{idx}"
            case _:
                return f"Expr({self.kind})"
    
    def __str__(self) -> str:
        return self.__repr__()
    
    def __eq__(self, other) -> bool:
        if not isinstance(other, Expr):
            return False
        return self.kind == other.kind
    
    def __hash__(self) -> int:
        return hash(str(self.kind))


# ===== 便捷别名 =====

# 常用 Sort
Expr.Prop = Expr.sort(Level.PROP)
Expr.Type = Expr.sort(Level.TYPE_0)
Expr.Type1 = Expr.sort(Level.TYPE_1)


def arrow(src: Expr, dst: Expr) -> Expr:
    """创建箭头类型 src → dst"""
    return Expr.mk_arrow(src, dst)


def forall_(name: str, dtype: Expr, body: Expr) -> Expr:
    """创建全称量词类型 Π name : dtype . body"""
    return Expr.forallE(name, dtype, body)


def lam(name: str, dtype: Expr, body: Expr) -> Expr:
    """创建 λ 抽象 λ name : dtype . body"""
    return Expr.lam(name, dtype, body)


def app(fn: Expr, *args: Expr) -> Expr:
    """创建多参数应用"""
    result = fn
    for arg in args:
        result = Expr.app(result, arg)
    return result
