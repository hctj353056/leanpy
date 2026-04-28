"""
归纳类型和 Recursor 自动生成模块。

这个模块实现了 Lean 归纳类型的核心机制：
1. 归纳类型声明（InductiveDecl）
2. 构造器（Constructor）
3. 消去子/归纳原理（Recursor）
4. Recursor 自动生成算法
5. 内置归纳类型（Nat, Bool, Unit, Empty）
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple, Union

from .name import Name, mk_name
from .level import Level
from .expr import Expr, BinderInfo
from .environment import (
    Environment, ConstantInfo,
    InductVal, CtorVal, RecVal,
    constant_info_name,
)


# ============================================================================
# 构造器（Constructor）
# ============================================================================

@dataclass(frozen=True)
class Constructor:
    """归纳类型的构造器。类型理论中的引入规则。"""
    name: Name
    type: Expr


# ============================================================================
# 归纳类型声明（InductiveDecl）
# ============================================================================

@dataclass
class InductiveDecl:
    """归纳类型声明，定义新类型及其构造器。"""
    name: Name
    level_params: List[str]
    num_params: int
    num_indices: int
    type: Expr
    constructors: List[Constructor]
    is_recursor: bool = False
    is_reflexive: bool = False

    def get_constructor_names(self) -> List[Name]:
        return [c.name for c in self.constructors]

    def get_recursor_name(self) -> Name:
        return self.name.append("rec")


# ============================================================================
# Recursor 计算规则（RecursorRule）
# ============================================================================

@dataclass(frozen=True)
class RecursorRule:
    """Recursor 的 ι-归约规则。"""
    ctor: Name
    nfields: int
    rhs: Expr


# ============================================================================
# 消去子（Recursor）
# ============================================================================

@dataclass
class Recursor:
    """消去子（recursor），归纳类型的消去规则。编码了归纳原理。"""
    name: Name
    type: Expr
    num_params: int
    num_indices: int
    num_motives: int
    num_minors: int
    rules: List[RecursorRule]
    is_k: bool = False
    level_params: List[str] = field(default_factory=list)

    def to_rec_val(self, induct_name: Name) -> RecVal:
        return RecVal(
            name=self.name, type=self.type, induct_name=induct_name,
            num_params=self.num_params, num_indices=self.num_indices,
            num_motives=self.num_motives, num_minors=self.num_minors,
            level_params=self.level_params, is_k=self.is_k,
        )


# ============================================================================
# 归纳类型环境扩展（InductiveEnvExt）
# ============================================================================

@dataclass
class InductiveEnvExt:
    """归纳类型环境扩展。"""
    inductives: Dict[Name, InductiveDecl] = field(default_factory=dict)
    recursors: Dict[Name, Name] = field(default_factory=dict)

    def add_inductive(self, decl: InductiveDecl, recursor: Recursor) -> InductiveEnvExt:
        new_inductives = dict(self.inductives)
        new_recursors = dict(self.recursors)
        new_inductives[decl.name] = decl
        new_recursors[decl.name] = recursor.name
        return InductiveEnvExt(new_inductives, new_recursors)

    def is_inductive(self, name: Name) -> bool:
        return name in self.inductives

    def get_inductive(self, name: Name) -> Optional[InductiveDecl]:
        return self.inductives.get(name)

    def get_recursor_name(self, induct_name: Name) -> Optional[Name]:
        return self.recursors.get(induct_name)


# ============================================================================
# 辅助函数
# ============================================================================

def _get_pi_binder_types(e: Expr) -> List[Tuple[str, Expr]]:
    """获取 Π-type 的所有绑定变量名和类型。"""
    result = []
    current = e
    while current.is_forallE():
        result.append((current.kind.name, current.kind.dtype))
        current = current.kind.body
    return result


def _shift_expr(e: Expr, delta: int) -> Expr:
    """将表达式中所有自由 bvar 索引增加 delta。"""
    if delta == 0:
        return e
    def go(expr: Expr, depth: int) -> Expr:
        match expr.kind:
            case Expr.BVar(idx):
                if idx >= depth:
                    return Expr.bvar(idx + delta)
                return expr
            case Expr.Lam(name, dtype, body, bi):
                return Expr.lam(name, go(dtype, depth), go(body, depth + 1), bi)
            case Expr.ForallE(name, dtype, body, bi):
                return Expr.forallE(name, go(dtype, depth), go(body, depth + 1), bi)
            case Expr.LetE(name, dtype, value, body):
                return Expr.letE(name, go(dtype, depth), go(value, depth), go(body, depth + 1))
            case Expr.App(fn, arg):
                return Expr.app(go(fn, depth), go(arg, depth))
            case Expr.Proj(tname, idx, struct):
                return Expr.proj(tname, idx, go(struct, depth))
            case _:
                return expr
    return go(e, 0)


# ============================================================================
# Recursor 类型和规则的直接构建
# ============================================================================

def _build_recursor_type_and_rules(
    induct_name: Name,
    induct_const: Expr,
    ctor_infos: List[Tuple[Name, Expr, int]],
) -> Tuple[Expr, List[RecursorRule]]:
    """
    直接构建 recursor 的完整类型和规则。

    使用命名上下文正确管理 bvar 索引。
    最终上下文（从内到外）: [t, minor_m, ..., minor_1, motive]
    所以: t=#0, minor_m=#1, ..., minor_1=#m, motive=#(m+1)
    """
    num_ctors = len(ctor_infos)
    u_sort = Expr.sort(Level.param("u"))

    # === 构建每个构造器的 minor premise 类型 ===
    # 在独立上下文中构建: 构造器参数 a_1...a_n 使用 bvar 0...n-1, motive = bvar(nfields)
    minor_types = []
    for ctor_idx, (ctor_name, ctor_type, nfields) in enumerate(ctor_infos):
        ctor_binders = _get_pi_binder_types(ctor_type)
        ctor_const = Expr.const(ctor_name, [])

        ctor_app = ctor_const
        for i in range(nfields):
            ctor_app = Expr.app(ctor_app, Expr.bvar(i))

        motive_app = Expr.app(Expr.bvar(nfields), ctor_app)
        minor_type = motive_app
        for i in range(nfields - 1, -1, -1):
            name, ftype = ctor_binders[i]
            minor_type = Expr.forallE(name, ftype, minor_type)

        minor_types.append(minor_type)

    # === 构建 recursor 类型（从内到外） ===
    # 最内层: motive t
    # t = #0, motive = #(num_ctors + 1) 因为有 num_ctors 个 minors 在 motive 和 t 之间
    # 加上 motive 本身一层，所以 motive = num_ctors + 1? 
    # 验证 Nat: num_ctors=2, [t, minor_2, minor_1, motive], motive=3 = num_ctors+1 ✓
    motive_idx = num_ctors + 1
    target_body = Expr.app(Expr.bvar(motive_idx), Expr.bvar(0))

    # Π t : I
    result = Expr.forallE("t", induct_const, target_body)

    # 从内到外添加 minor premises
    rules = []
    for ctor_idx in range(num_ctors - 1, -1, -1):
        ctor_name, ctor_type, nfields = ctor_infos[ctor_idx]
        minor_name = f"minor_{ctor_idx + 1}"

        # minor premise 类型中的 motive 索引需要调整。
        # 在独立上下文中 motive = #nfields。
        # 在 `Π minor_{ctor_idx+1} : TYPE` 的 TYPE 中：
        #   自动跳过 minor_{ctor_idx+1} 后，motive 前面有 ctor_idx 个其他 minors。
        #   所以 motive = #(nfields + ctor_idx)。
        #   偏移量 = (nfields + ctor_idx) - nfields = ctor_idx。
        shifted_minor = _shift_expr(minor_types[ctor_idx], ctor_idx)
        result = Expr.forallE(minor_name, shifted_minor, result)

        # rule rhs: 此 minor 在最终上下文中的 bvar 索引
        # [t, minor_m, ..., minor_1, motive]
        # minor_{ctor_idx+1} 的索引 = num_ctors - ctor_idx
        minor_bvar_idx = num_ctors - ctor_idx

        if nfields == 0:
            rhs = Expr.bvar(minor_bvar_idx)
        else:
            rhs = Expr.bvar(minor_bvar_idx)
            for i in range(nfields):
                rhs = Expr.app(rhs, Expr.bvar(nfields - 1 - i))

        rules.append(RecursorRule(ctor=ctor_name, nfields=nfields, rhs=rhs))

    # 最外层: Π motive : (I -> Sort u)
    motive_type = Expr.mk_arrow(induct_const, u_sort)
    result = Expr.forallE("motive", motive_type, result, BinderInfo.IMPLICIT)

    rules.reverse()
    return result, rules


# ============================================================================
# 内置归纳类型创建辅助函数
# ============================================================================

def mk_nat_type() -> Tuple[InductiveDecl, List[ConstantInfo]]:
    """创建自然数类型 Nat 及其所有声明。"""
    nat_name = mk_name("Nat")
    nat_type_expr = Expr.Type
    nat_const = Expr.const(nat_name)

    zero_name = nat_name.append("zero")
    zero_type = Expr.const(nat_name)

    succ_name = nat_name.append("succ")
    succ_type = Expr.forallE("n", Expr.const(nat_name), Expr.const(nat_name))

    nat_ind = InductiveDecl(
        name=nat_name, level_params=[], num_params=0, num_indices=0,
        type=nat_type_expr,
        constructors=[
            Constructor(name=zero_name, type=zero_type),
            Constructor(name=succ_name, type=succ_type),
        ],
        is_recursor=True,
    )

    ctor_infos = [(zero_name, zero_type, 0), (succ_name, succ_type, 1)]
    rec_type, rules = _build_recursor_type_and_rules(nat_name, nat_const, ctor_infos)

    nat_rec = Recursor(
        name=nat_ind.get_recursor_name(), type=rec_type,
        num_params=0, num_indices=0, num_motives=1, num_minors=2,
        rules=rules, level_params=["u"],
    )

    constants: List[ConstantInfo] = [
        InductVal(name=nat_name, type=nat_type_expr, num_params=0, num_indices=0,
                  all_ctor_names=[zero_name, succ_name]),
        CtorVal(name=zero_name, type=zero_type, induct_name=nat_name,
                cidx=1, num_params=0, num_fields=0),
        CtorVal(name=succ_name, type=succ_type, induct_name=nat_name,
                cidx=2, num_params=0, num_fields=1),
        nat_rec.to_rec_val(nat_name),
    ]

    return nat_ind, constants


def mk_bool_type() -> Tuple[InductiveDecl, List[ConstantInfo]]:
    """创建布尔类型 Bool 及其所有声明。"""
    bool_name = mk_name("Bool")
    bool_type_expr = Expr.Type
    bool_const = Expr.const(bool_name)

    false_name = bool_name.append("false")
    false_type = Expr.const(bool_name)

    true_name = bool_name.append("true")
    true_type = Expr.const(bool_name)

    bool_ind = InductiveDecl(
        name=bool_name, level_params=[], num_params=0, num_indices=0,
        type=bool_type_expr,
        constructors=[
            Constructor(name=false_name, type=false_type),
            Constructor(name=true_name, type=true_type),
        ],
        is_recursor=False,
    )

    ctor_infos = [(false_name, false_type, 0), (true_name, true_type, 0)]
    rec_type, rules = _build_recursor_type_and_rules(bool_name, bool_const, ctor_infos)

    bool_rec = Recursor(
        name=bool_ind.get_recursor_name(), type=rec_type,
        num_params=0, num_indices=0, num_motives=1, num_minors=2,
        rules=rules, level_params=["u"],
    )

    constants: List[ConstantInfo] = [
        InductVal(name=bool_name, type=bool_type_expr, num_params=0, num_indices=0,
                  all_ctor_names=[false_name, true_name]),
        CtorVal(name=false_name, type=false_type, induct_name=bool_name,
                cidx=1, num_params=0, num_fields=0),
        CtorVal(name=true_name, type=true_type, induct_name=bool_name,
                cidx=2, num_params=0, num_fields=0),
        bool_rec.to_rec_val(bool_name),
    ]

    return bool_ind, constants


def mk_unit_type() -> Tuple[InductiveDecl, List[ConstantInfo]]:
    """创建单位类型 Unit（对应逻辑中的 True）。"""
    unit_name = mk_name("Unit")
    unit_type_expr = Expr.Type
    unit_const = Expr.const(unit_name)

    unit_ctor_name = unit_name.append("unit")
    unit_ctor_type = Expr.const(unit_name)

    unit_ind = InductiveDecl(
        name=unit_name, level_params=[], num_params=0, num_indices=0,
        type=unit_type_expr,
        constructors=[Constructor(name=unit_ctor_name, type=unit_ctor_type)],
        is_recursor=False,
    )

    ctor_infos = [(unit_ctor_name, unit_ctor_type, 0)]
    rec_type, rules = _build_recursor_type_and_rules(unit_name, unit_const, ctor_infos)

    unit_rec = Recursor(
        name=unit_ind.get_recursor_name(), type=rec_type,
        num_params=0, num_indices=0, num_motives=1, num_minors=1,
        rules=rules, level_params=["u"],
    )

    constants: List[ConstantInfo] = [
        InductVal(name=unit_name, type=unit_type_expr, num_params=0, num_indices=0,
                  all_ctor_names=[unit_ctor_name]),
        CtorVal(name=unit_ctor_name, type=unit_ctor_type, induct_name=unit_name,
                cidx=1, num_params=0, num_fields=0),
        unit_rec.to_rec_val(unit_name),
    ]

    return unit_ind, constants


def mk_empty_type() -> Tuple[InductiveDecl, List[ConstantInfo]]:
    """创建空类型 Empty（对应逻辑中的 False，爆炸原理）。"""
    empty_name = mk_name("Empty")
    empty_type_expr = Expr.Type
    empty_const = Expr.const(empty_name)

    empty_ind = InductiveDecl(
        name=empty_name, level_params=[], num_params=0, num_indices=0,
        type=empty_type_expr,
        constructors=[],
        is_recursor=False,
    )

    # Empty.rec: Π motive : (Empty → Sort u), Π e : Empty, motive e
    u_sort = Expr.sort(Level.param("u"))
    motive_type = Expr.mk_arrow(empty_const, u_sort)
    target_body = Expr.app(Expr.bvar(1), Expr.bvar(0))  # motive e
    rec_type = Expr.forallE("motive", motive_type,
                    Expr.forallE("e", empty_const, target_body),
                    BinderInfo.IMPLICIT)

    empty_rec = Recursor(
        name=empty_ind.get_recursor_name(), type=rec_type,
        num_params=0, num_indices=0, num_motives=1, num_minors=0,
        rules=[], level_params=["u"],
    )

    constants: List[ConstantInfo] = [
        InductVal(name=empty_name, type=empty_type_expr, num_params=0, num_indices=0,
                  all_ctor_names=[]),
        empty_rec.to_rec_val(empty_name),
    ]

    return empty_ind, constants


# ============================================================================
# 通用 Recursor 生成接口
# ============================================================================

def generate_recursor(ind: InductiveDecl, env: Optional[Environment] = None) -> Recursor:
    """为归纳类型自动生成 recursor。"""
    induct_const = Expr.const(ind.name, [])
    ctor_infos = []
    for ctor in ind.constructors:
        ctor_binders = _get_pi_binder_types(ctor.type)
        ctor_infos.append((ctor.name, ctor.type, len(ctor_binders)))

    rec_type, rules = _build_recursor_type_and_rules(ind.name, induct_const, ctor_infos)

    return Recursor(
        name=ind.get_recursor_name(), type=rec_type,
        num_params=ind.num_params, num_indices=ind.num_indices,
        num_motives=1, num_minors=len(ind.constructors),
        rules=rules, is_k=False,
        level_params=ind.level_params + ["u"],
    )


# ============================================================================
# 环境注册辅助函数
# ============================================================================

def register_inductive(env: Environment, decl: InductiveDecl,
                       constants: List[ConstantInfo]) -> Environment:
    """将归纳类型的所有常量注册到全局环境。"""
    new_env = env
    for const in constants:
        name = constant_info_name(const)
        new_env = new_env.add(name, const)
    return new_env


def mk_env_with_nats() -> Environment:
    """创建包含自然数类型的全局环境。"""
    env = Environment()
    _, constants = mk_nat_type()
    return register_inductive(env, _, constants)


def mk_env_with_bools() -> Environment:
    """创建包含布尔类型的全局环境。"""
    env = Environment()
    _, constants = mk_bool_type()
    return register_inductive(env, _, constants)


def mk_env_with_all_builtins() -> Environment:
    """创建包含所有内置类型（Nat, Bool, Unit, Empty）的全局环境。"""
    env = Environment()
    for mk_fn in [mk_nat_type, mk_bool_type, mk_unit_type, mk_empty_type]:
        _, constants = mk_fn()
        for const in constants:
            name = constant_info_name(const)
            env = env.add(name, const)
    return env


# ============================================================================
# 积类型 (Prod / A × B)
# ============================================================================

def mk_prod_type() -> Tuple[InductiveDecl, List[ConstantInfo]]:
    """创建积类型 Prod A B（即 A × B，对应逻辑合取 A ∧ B）。
    
    inductive Prod (A : Type u) (B : Type v) : Type (max u v) where
      | mk : A → B → Prod A B
    """
    u_level = Level.param("u")
    v_level = Level.param("v")
    uv_level = Level.max_level(u_level, v_level)
    
    prod_name = mk_name("Prod")
    A_name = mk_name("A")
    B_name = mk_name("B")
    
    # A : Type u
    A_type = Expr.sort(u_level)
    # B : Type v
    B_type = Expr.sort(v_level)
    # Prod A B : Type (max u v)
    prod_AB = Expr.mk_app(Expr.const(prod_name, [u_level, v_level]),
                          [Expr.const(A_name), Expr.const(B_name)])
    
    # Prod 的类型: Π (A : Type u) (B : Type v), Type (max u v)
    prod_type = Expr.forallE("A", A_type,
        Expr.forallE("B", B_type,
            Expr.sort(uv_level)))
    
    # mk : Π (A : Type u) (B : Type v), A → B → Prod A B
    A_const = Expr.const(A_name)
    B_const = Expr.const(B_name)
    mk_type = Expr.forallE("A", A_type,
        Expr.forallE("B", B_type,
            Expr.forallE("a", A_const,
                Expr.forallE("b", B_const,
                    Expr.mk_app(
                        Expr.const(prod_name, [u_level, v_level]),
                        [A_const, B_const])))))
    
    ctor = Constructor(name=mk_name("Prod", "mk"), type=mk_type)
    
    prod_ind = InductiveDecl(
        name=prod_name, level_params=["u", "v"],
        num_params=2, num_indices=0,
        type=prod_type, constructors=[ctor],
        is_recursor=False,
    )
    
    prod_rec = generate_recursor(prod_ind)
    
    constants: List[ConstantInfo] = [
        InductVal(name=prod_name, type=prod_type, num_params=2, num_indices=0,
                  all_ctor_names=[mk_name("Prod", "mk")], is_rec=False),
        CtorVal(name=mk_name("Prod", "mk"), type=mk_type,
                induct_name=prod_name, cidx=1, num_params=2, num_fields=2),
        prod_rec.to_rec_val(prod_name),
    ]
    
    return prod_ind, constants


# ============================================================================
# 和类型 (Sum / A ⊕ B)
# ============================================================================

def mk_sum_type() -> Tuple[InductiveDecl, List[ConstantInfo]]:
    """创建和类型 Sum A B（即 A ⊕ B，对应逻辑析取 A ∨ B）。
    
    inductive Sum (A : Type u) (B : Type v) : Type (max u v) where
      | inl : A → Sum A B
      | inr : B → Sum A B
    """
    u_level = Level.param("u")
    v_level = Level.param("v")
    uv_level = Level.max_level(u_level, v_level)
    
    sum_name = mk_name("Sum")
    A_name = mk_name("A")
    B_name = mk_name("B")
    
    A_type = Expr.sort(u_level)
    B_type = Expr.sort(v_level)
    
    # Sum A B : Type (max u v)
    sum_AB = Expr.mk_app(Expr.const(sum_name, [u_level, v_level]),
                         [Expr.const(A_name), Expr.const(B_name)])
    
    # Sum 的类型: Π (A : Type u) (B : Type v), Type (max u v)
    sum_type = Expr.forallE("A", A_type,
        Expr.forallE("B", B_type,
            Expr.sort(uv_level)))
    
    A_const = Expr.const(A_name)
    B_const = Expr.const(B_name)
    
    # inl : Π (A : Type u) (B : Type v), A → Sum A B
    inl_type = Expr.forallE("A", A_type,
        Expr.forallE("B", B_type,
            Expr.forallE("a", A_const,
                Expr.mk_app(
                    Expr.const(sum_name, [u_level, v_level]),
                    [A_const, B_const]))))
    
    # inr : Π (A : Type u) (B : Type v), B → Sum A B
    inr_type = Expr.forallE("A", A_type,
        Expr.forallE("B", B_type,
            Expr.forallE("b", B_const,
                Expr.mk_app(
                    Expr.const(sum_name, [u_level, v_level]),
                    [A_const, B_const]))))
    
    inl_ctor = Constructor(name=mk_name("Sum", "inl"), type=inl_type)
    inr_ctor = Constructor(name=mk_name("Sum", "inr"), type=inr_type)
    
    sum_ind = InductiveDecl(
        name=sum_name, level_params=["u", "v"],
        num_params=2, num_indices=0,
        type=sum_type, constructors=[inl_ctor, inr_ctor],
        is_recursor=False,
    )
    
    sum_rec = generate_recursor(sum_ind)
    
    constants: List[ConstantInfo] = [
        InductVal(name=sum_name, type=sum_type, num_params=2, num_indices=0,
                  all_ctor_names=[mk_name("Sum", "inl"), mk_name("Sum", "inr")], is_rec=False),
        CtorVal(name=mk_name("Sum", "inl"), type=inl_type,
                induct_name=sum_name, cidx=1, num_params=2, num_fields=1),
        CtorVal(name=mk_name("Sum", "inr"), type=inr_type,
                induct_name=sum_name, cidx=2, num_params=2, num_fields=1),
        sum_rec.to_rec_val(sum_name),
    ]
    
    return sum_ind, constants
