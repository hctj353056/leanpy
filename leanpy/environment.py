"""
Lean 全局环境和局部上下文模块。

这个模块实现了 Lean 定理证明器的环境管理，包括：
1. 全局常量信息（ConstantInfo）- 存储公理、定义、定理、归纳类型等
2. 全局环境（Environment）- 存储所有已声明的全局常量
3. 局部上下文（LocalContext）- 存储局部变量和假设
4. 元变量上下文（MetavarContext）- 管理未解决的证明目标（"洞"）

类型理论含义：
- 全局环境对应于类型理论的签名（signature），包含所有已声明的常量和其类型
- 局部上下文对应于类型判断的上下文 Γ，在类型推导中累积假设
- 元变量上下文对应于证明搜索中的开放目标（open goals）
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Union

from .name import Name
from .expr import Expr, BinderInfo


# ============================================================================
# 全局常量信息（ConstantInfo）
# ============================================================================

@dataclass(frozen=True)
class AxiomVal:
    """
    公理声明。

    类型理论含义：公理是签名中的一项，断言某个类型是可居住的（inhabited），
    但不提供具体的居住者（证明/项）。
    例如：axiom choice : Π (A : Type), nonempty A → A

    在 Lean 中，公理与定义的区别在于公理没有定义体（没有计算行为）。
    """
    name: Name        # 公理名称
    type: Expr        # 公理类型
    level_params: List[str] = field(default_factory=list)  # universe 参数


@dataclass(frozen=True)
class DefnVal:
    """
    定义（透明定义）。

    类型理论含义：定义是签名中的一项，给某个名称赋了一个类型和一个项（定义体）。
    定义是"透明的"，意味着在类型检查和证明中可以被展开（δ-归约）。
    例如：def double (n : Nat) : Nat := n + n

    字段 is_opaque=False 表示这是透明定义。
    """
    name: Name
    type: Expr
    value: Expr       # 定义体（实际的项）
    level_params: List[str] = field(default_factory=list)
    is_opaque: bool = False  # 是否不透明（默认可展开）


@dataclass(frozen=True)
class ThmVal:
    """
    定理声明。

    类型理论含义：在 Curry-Howard 同构下，定理就是类型，证明就是项。
    ThmVal 存储了一个命题（type）及其证明（value）。
    与 DefnVal 的区别在于定理的证明在计算中被视为不透明的（proof irrelevance）。

    例如：theorem add_zero : ∀ n, n + 0 = n := ...
    """
    name: Name
    type: Expr        # 定理陈述（命题）
    value: Expr       # 证明项
    level_params: List[str] = field(default_factory=list)


@dataclass(frozen=True)
class OpaqueVal:
    """
    不透明定义。

    类型理论含义：与 DefnVal 类似，但定义体不可展开。
    这在需要隐藏实现细节时使用（如抽象数据类型）。
    不透明定义在类型检查中只能以其声明的类型使用，不能 δ-归约。
    """
    name: Name
    type: Expr
    value: Optional[Expr] = None  # 可能有无定义体，但不允许展开
    level_params: List[str] = field(default_factory=list)


@dataclass(frozen=True)
class InductVal:
    """
    归纳类型声明。

    类型理论含义：归纳类型是类型理论中最强大的构造之一，
    允许通过构造器（constructors）来定义新的类型。
    每个归纳类型都对应一个消去子（recursor），提供归纳证明和递归定义的能力。

    例如：
      inductive Nat
        | zero : Nat
        | succ : Nat → Nat
    """
    name: Name                    # 归纳类型名称（如 Nat）
    type: Expr                    # 归纳类型本身的类型（如 Type）
    num_params: int               # 参数数量（如 Nat 有 0 个参数；List 有 1 个参数）
    num_indices: int              # 索引数量（如 Vec A n 有 1 个索引 n）
    all_ctor_names: List[Name]    # 所有构造器名称列表
    level_params: List[str] = field(default_factory=list)
    is_rec: bool = False          # 是否是递归类型（构造器参数中包含自身）
    is_reflexive: bool = False    # 是否是自反类型


@dataclass(frozen=True)
class CtorVal:
    """
    构造器声明。

    类型理论含义：构造器是归纳类型的引入规则（introduction rule）。
    每个构造器 c 的类型形如：
      Π (p₁:P₁)...(pₙ:Pₙ) (a₁:A₁)...(aₘ:Aₘ), I p₁...pₙ t₁...tₖ
    其中 I 是归纳类型，pᵢ 是参数，aⱼ 是构造器参数（字段），tₗ 是索引项。

    例如 Nat.succ : Nat → Nat
    """
    name: Name           # 构造器名称（如 Nat.succ）
    type: Expr           # 构造器的完整类型（Π-type）
    induct_name: Name    # 所属的归纳类型名称
    cidx: int            # 构造器索引（第几个构造器，从 1 开始）
    num_params: int      # 归纳类型的参数数量
    num_fields: int      # 构造器的字段数（递归参数 + 非递归参数）
    level_params: List[str] = field(default_factory=list)


@dataclass(frozen=True)
class RecVal:
    """
    消去子（recursor）声明。

    类型理论含义：消去子是归纳类型的消去规则（elimination rule），
    对应于归纳原理（induction principle）。
    每个归纳类型自动生成一个 recursor，用于：
    - 递归定义（通过构造器定义函数）
    - 归纳证明（证明对所有归纳类型的元素成立的性质）

    例如 Nat.rec（归纳原理）：
      Π {motive : Nat → Sort u},
        motive zero →
        (Π n, motive n → motive (succ n)) →
        Π t, motive t

    其中 motive 是归纳假设/目标，每个构造器对应一个分支。
    """
    name: Name            # recursor 名称（如 Nat.rec）
    type: Expr            # recursor 的完整类型
    induct_name: Name     # 对应的归纳类型
    num_params: int       # 参数数
    num_indices: int      # 索引数
    num_motives: int      # motive 数量（通常为 1）
    num_minors: int       # 归纳分支数（= 构造器数量）
    level_params: List[str] = field(default_factory=list)
    is_k: bool = False    # 是否是 K-like recursor（ proof-irrelevant ）


# ConstantInfo 是上述所有常量类型的联合
ConstantInfo = Union[AxiomVal, DefnVal, ThmVal, OpaqueVal, InductVal, CtorVal, RecVal]


def constant_info_name(info: ConstantInfo) -> Name:
    """获取 ConstantInfo 的名称（辅助函数）"""
    match info:
        case (
            AxiomVal(name=n) | DefnVal(name=n) | ThmVal(name=n) |
            OpaqueVal(name=n) | InductVal(name=n) | CtorVal(name=n) | RecVal(name=n)
        ):
            return n


def constant_info_type(info: ConstantInfo) -> Expr:
    """获取 ConstantInfo 的类型（辅助函数）"""
    match info:
        case (
            AxiomVal(type=t) | DefnVal(type=t) | ThmVal(type=t) |
            OpaqueVal(type=t) | InductVal(type=t) | CtorVal(type=t) | RecVal(type=t)
        ):
            return t


# ============================================================================
# 全局环境（Environment）
# ============================================================================

@dataclass
class Environment:
    """
    全局环境，存储所有已声明的全局常量。

    类型理论含义：全局环境对应于类型理论的签名（signature），
    它是一个从名称到常量信息的映射。每个常量都有唯一的全局名称和类型。

    在 Lean 中，环境是函数式更新的（immutable），这使得回溯和增量检查成为可能。
    我们用 Python 的 dataclass 配合字典复制来模拟这种函数式语义。

    字段：
    - constants: 所有全局常量的映射
    - extensions: 环境扩展（如归纳类型注册表）
    """
    constants: Dict[Name, ConstantInfo] = field(default_factory=dict)

    def add(self, name: Name, info: ConstantInfo) -> Environment:
        """
        添加全局常量（函数式更新）。

        返回一个新环境，包含原有常量加上新常量。
        如果名称已存在，新的声明会覆盖旧的（用于增量编译中的重新定义）。

        类型理论含义：扩展签名，添加一个新的常量声明。
        """
        new_constants = dict(self.constants)
        new_constants[name] = info
        return Environment(new_constants)

    def lookup(self, name: Name) -> Optional[ConstantInfo]:
        """
        查找全局常量。

        如果找到，返回对应的 ConstantInfo；否则返回 None。
        """
        return self.constants.get(name)

    def contains(self, name: Name) -> bool:
        """
        检查全局常量是否存在。
        """
        return name in self.constants

    def is_opaque(self, name: Name) -> bool:
        """
        检查常量是否不透明（不能展开）。

        公理、定理、不透明定义都是不透明的。
        透明定义和普通构造器是可展开的。
        """
        info = self.lookup(name)
        if info is None:
            return False
        match info:
            case AxiomVal() | ThmVal() | OpaqueVal():
                return True
            case DefnVal(is_opaque=opaque):
                return opaque
            case CtorVal() | RecVal() | InductVal():
                # 构造器、recursor 和归纳类型本身在 δ-归约中不展开
                return True
            case _:
                return False

    def get_type(self, name: Name) -> Optional[Expr]:
        """获取常量的类型"""
        info = self.lookup(name)
        if info is None:
            return None
        return constant_info_type(info)

    def __repr__(self) -> str:
        lines = ["Environment {"]
        for name in sorted([str(n) for n in self.constants.keys()]):
            lines.append(f"  {name}")
        lines.append("}")
        return "\n".join(lines)


# ============================================================================
# 局部声明（LocalDecl）
# ============================================================================

@dataclass(frozen=True)
class LocalDecl:
    """
    局部声明，表示局部上下文中的一个条目。

    类型理论含义：局部声明对应于类型推导上下文 Γ 中的一个假设或定义。
    在类型判断 Γ ⊢ e : A 中，Γ 由一系列局部声明组成。

    局部声明有两种形式：
    - cdecl（regular declaration）: x : A —— 假设 x 具有类型 A
    - ldecl（let declaration）: x : A := v —— 定义 x 为类型 A 的值 v

    每个局部声明都有一个唯一的 fvar_id，用于在表达式中引用（通过 Expr.FVar）。
    """

    @dataclass(frozen=True)
    class CDecl:
        """常规声明：假设/参数 x : A"""
        pass

    @dataclass(frozen=True)
    class LDecl:
        """Let 绑定声明：x : A := v"""
        pass

    # 联合类型
    decl_type: Union[CDecl, LDecl]
    fvar_id: int       # 唯一标识符（对应 Expr.FVar 的 id）
    user_name: str     # 用户提供的名称（用于显示）
    type: Expr         # 声明的类型
    value: Optional[Expr] = None  # let 绑定的值（cdecl 为 None）
    binder_info: BinderInfo = BinderInfo.DEFAULT  # 绑定器信息

    @staticmethod
    def cdecl(fvar_id: int, user_name: str, type: Expr,
              binder_info: BinderInfo = BinderInfo.DEFAULT) -> LocalDecl:
        """创建常规声明（cdecl）：x : A"""
        return LocalDecl(LocalDecl.CDecl(), fvar_id, user_name, type, None, binder_info)

    @staticmethod
    def ldecl(fvar_id: int, user_name: str, type: Expr, value: Expr) -> LocalDecl:
        """创建 let 绑定声明（ldecl）：x : A := v"""
        return LocalDecl(
            LocalDecl.LDecl(), fvar_id, user_name, type, value, BinderInfo.DEFAULT
        )

    def is_let(self) -> bool:
        """是否是 let 绑定"""
        return isinstance(self.decl_type, LocalDecl.LDecl)

    def to_expr(self) -> Expr:
        """将此声明转换为 FVar 表达式"""
        return Expr.fvar(self.fvar_id)


# ============================================================================
# 局部上下文（LocalContext）
# ============================================================================

@dataclass
class LocalContext:
    """
    局部上下文，存储类型推导过程中累积的假设和定义。

    类型理论含义：局部上下文对应于类型理论中的上下文 Γ。
    在推导 Γ ⊢ e : A 时，Γ 是一个有序的假设列表。

    重要约定（de Bruijn 索引）：
    - 局部上下文中的声明按加入顺序存储
    - 最后加入的声明对应 de Bruijn 索引 #0
    - 这在实现上与 Lean 的局部上下文一致

    局部上下文支持函数式更新，每次扩展返回新对象。
    """
    decls: List[LocalDecl] = field(default_factory=list)
    _next_fvar_id: int = field(default=0, repr=False)

    def extend(self, decl: LocalDecl) -> LocalContext:
        """
        扩展局部上下文（函数式更新）。

        将一个新的局部声明添加到上下文末尾。
        返回新的 LocalContext，不影响原对象。

        类型理论含义：Γ, x:A ⊢ ... 中的上下文扩展。
        """
        new_decls = list(self.decls)
        new_decls.append(decl)
        return LocalContext(new_decls, max(self._next_fvar_id, decl.fvar_id + 1))

    def extend_cdecl(
        self, user_name: str, type: Expr,
        binder_info: BinderInfo = BinderInfo.DEFAULT
    ) -> Tuple[LocalContext, Expr]:
        """
        创建 cdecl 并扩展上下文。

        自动分配 fvar_id，返回 (新上下文, fvar 表达式)。
        这是常用的便捷方法。
        """
        fvar_id = self._next_fvar_id
        decl = LocalDecl.cdecl(fvar_id, user_name, type, binder_info)
        new_ctx = self.extend(decl)
        return new_ctx, Expr.fvar(fvar_id)

    def extend_ldecl(
        self, user_name: str, type: Expr, value: Expr
    ) -> Tuple[LocalContext, Expr]:
        """
        创建 ldecl 并扩展上下文。

        自动分配 fvar_id，返回 (新上下文, fvar 表达式)。
        """
        fvar_id = self._next_fvar_id
        decl = LocalDecl.ldecl(fvar_id, user_name, type, value)
        new_ctx = self.extend(decl)
        return new_ctx, Expr.fvar(fvar_id)

    def mk_fvar(
        self, user_name: str, type: Expr,
        binder_info: BinderInfo = BinderInfo.DEFAULT
    ) -> Tuple[LocalContext, Expr]:
        """
        创建新的自由变量并加入上下文（别名）。

        返回 (新上下文, fvar 表达式)。
        """
        return self.extend_cdecl(user_name, type, binder_info)

    def get_decl(self, fvar_id: int) -> Optional[LocalDecl]:
        """
        通过 fvar_id 查找局部声明。
        """
        for decl in self.decls:
            if decl.fvar_id == fvar_id:
                return decl
        return None

    def get_type(self, fvar_id: int) -> Optional[Expr]:
        """
        获取自由变量的类型。
        """
        decl = self.get_decl(fvar_id)
        return decl.type if decl else None

    def get_value(self, fvar_id: int) -> Optional[Expr]:
        """
        获取 let 绑定变量的值。
        """
        decl = self.get_decl(fvar_id)
        return decl.value if decl else None

    def length(self) -> int:
        """返回局部上下文中的声明数量"""
        return len(self.decls)

    def is_empty(self) -> bool:
        """检查局部上下文是否为空"""
        return len(self.decls) == 0

    def get_fvar_ids(self) -> List[int]:
        """获取所有 fvar_id 的列表"""
        return [decl.fvar_id for decl in self.decls]

    def get_fvars(self) -> List[Expr]:
        """获取所有 fvar 表达式的列表"""
        return [Expr.fvar(decl.fvar_id) for decl in self.decls]

    def __repr__(self) -> str:
        lines = ["LocalContext {"]
        for decl in self.decls:
            name = decl.user_name
            if decl.is_let():
                lines.append(f"  let {name} : {decl.type} := {decl.value}")
            else:
                lines.append(f"  {name} : {decl.type}")
        lines.append("}")
        return "\n".join(lines)


# ============================================================================
# 元变量声明（MetavarDecl）
# ============================================================================

@dataclass(frozen=True)
class MetavarDecl:
    """
    元变量声明，表示一个待填充的"洞"。

    类型理论含义：元变量对应于证明搜索中的开放目标（open goal）。
    在交互式定理证明中，当用户声明一个定理但尚未提供证明时，
    系统创建一个元变量来表示这个"待填充的证明"。

    每个元变量都在特定的局部上下文中定义，这确保了元变量的解
    只能使用该上下文中可用的变量。

    字段：
    - mvar_id: 唯一标识符
    - local_context: 元变量定义时的局部上下文（确定可用变量）
    - type: 元变量的类型（需要填充的项的类型）
    - user_name: 可选的用户提供的名称（用于显示）
    """
    mvar_id: int
    local_context: LocalContext
    type: Expr
    user_name: Optional[str] = None

    def to_expr(self) -> Expr:
        """将此声明转换为 MVar 表达式"""
        return Expr.mvar(self.mvar_id)


# ============================================================================
# 元变量上下文（MetavarContext）
# ============================================================================

@dataclass
class MetavarContext:
    """
    元变量上下文，管理所有未解决的元变量及其赋值。

    类型理论含义：元变量上下文是证明搜索状态的核心。
    它跟踪所有"开放目标"（未赋值的元变量）以及已被解决的元变量。

    在 tactic 系统中：
    - 未赋值的元变量 = 待证明的目标
    - 已赋值的元变量 = 已找到证明的目标
    - instantiate_mvars = 将所有已解决的元变量替换为其实际值

    字段：
    - decls: 所有元变量的声明（包括已赋值和未赋值的）
    - assignments: 已赋值的元变量的映射 mvar_id → Expr
    """
    decls: Dict[int, MetavarDecl] = field(default_factory=dict)
    assignments: Dict[int, Expr] = field(default_factory=dict)
    _next_mvar_id: int = field(default=0, repr=False)

    def add(self, local_ctx: LocalContext, type: Expr,
            user_name: Optional[str] = None) -> Tuple[MetavarContext, Expr]:
        """
        添加新的元变量。

        在指定的局部上下文中创建一个类型为 type 的新元变量。
        返回 (新上下文, MVar 表达式)。

        类型理论含义：声明一个新的开放目标，其证明可以在 local_ctx 中构造。
        """
        mvar_id = self._next_mvar_id
        decl = MetavarDecl(mvar_id, local_ctx, type, user_name)
        new_decls = dict(self.decls)
        new_decls[mvar_id] = decl
        new_ctx = MetavarContext(new_decls, dict(self.assignments), mvar_id + 1)
        return new_ctx, Expr.mvar(mvar_id)

    def add_decl(
        self, mvar_id: int, local_ctx: LocalContext, type: Expr,
        user_name: Optional[str] = None
    ) -> MetavarContext:
        """通过指定 ID 添加元变量声明"""
        decl = MetavarDecl(mvar_id, local_ctx, type, user_name)
        new_decls = dict(self.decls)
        new_decls[mvar_id] = decl
        return MetavarContext(
            new_decls, dict(self.assignments),
            max(self._next_mvar_id, mvar_id + 1)
        )

    def assign(self, mvar_id: int, value: Expr) -> MetavarContext:
        """
        为元变量赋值。

        将元变量 mvar_id 的解设为 value。
        返回新上下文（函数式更新）。

        类型理论含义：找到了开放目标的证明/项，记录这个解。
        value 必须满足 decls[mvar_id].local_context ⊢ value : decls[mvar_id].type。

        前提条件：元变量必须已被声明且未被赋值。
        """
        if mvar_id not in self.decls:
            raise ValueError(f"未声明的元变量: ?{mvar_id}")
        if mvar_id in self.assignments:
            raise ValueError(f"元变量 ?{mvar_id} 已被赋值")
        new_assignments = dict(self.assignments)
        new_assignments[mvar_id] = value
        return MetavarContext(dict(self.decls), new_assignments, self._next_mvar_id)

    def get_assignment(self, mvar_id: int) -> Optional[Expr]:
        """
        获取元变量的赋值（如果已赋值）。
        """
        return self.assignments.get(mvar_id)

    def is_assigned(self, mvar_id: int) -> bool:
        """
        检查元变量是否已被赋值。
        """
        return mvar_id in self.assignments

    def get_decl(self, mvar_id: int) -> Optional[MetavarDecl]:
        """获取元变量声明"""
        return self.decls.get(mvar_id)

    def instantiate_mvars(self, expr: Expr) -> Expr:
        """
        实例化表达式中的所有元变量。

        将表达式中所有已赋值的 MVar 替换为对应的值。
        这是一个深度优先遍历，会递归处理替换后的表达式中可能出现的新元变量。

        类型理论含义：将"部分完成的证明"推进为"更完整的证明"，
        通过填充所有已经找到的解。

        例如：如果 ?1 := Nat.zero，则 instantiate_mvars (?1 + 2) = Nat.zero + 2
        """
        def go(e: Expr) -> Expr:
            match e.kind:
                case Expr.MVar(id):
                    # 如果这个元变量已赋值，递归实例化其值
                    assignment = self.assignments.get(id)
                    if assignment is not None:
                        return go(assignment)
                    return e
                case Expr.App(fn, arg):
                    return Expr.app(go(fn), go(arg))
                case Expr.Lam(name, dtype, body, bi):
                    return Expr.lam(name, go(dtype), go(body), bi)
                case Expr.ForallE(name, dtype, body, bi):
                    return Expr.forallE(name, go(dtype), go(body), bi)
                case Expr.LetE(name, dtype, value, body):
                    return Expr.letE(name, go(dtype), go(value), go(body))
                case Expr.Proj(tname, idx, struct):
                    return Expr.Proj(tname, idx, go(struct))
                case _:
                    # BVar, FVar, Sort, Const, Lit 不含子表达式中的元变量
                    return e
        return go(expr)

    def get_unassigned(self) -> List[int]:
        """
        获取所有未赋值的元变量 ID。

        这是 tactic 系统需要解决的所有开放目标。
        """
        return [mvar_id for mvar_id in self.decls if mvar_id not in self.assignments]

    def is_solved(self) -> bool:
        """检查所有元变量是否都已赋值"""
        return len(self.get_unassigned()) == 0

    def __repr__(self) -> str:
        lines = ["MetavarContext {"]
        lines.append(f"  已声明: {list(self.decls.keys())}")
        lines.append(f"  已赋值: {dict(self.assignments)}")
        lines.append("}")
        return "\n".join(lines)


# ============================================================================
# 便捷函数
# ============================================================================

def mk_empty_env() -> Environment:
    """创建空的全局环境"""
    return Environment()


def mk_empty_lctx() -> LocalContext:
    """创建空的局部上下文"""
    return LocalContext()


def mk_empty_mctx() -> MetavarContext:
    """创建空的元变量上下文"""
    return MetavarContext()
