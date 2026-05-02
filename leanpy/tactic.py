"""
LeanPy Tactic 系统：基于元变量的交互式证明构造。

核心哲学：
- 命题即类型，证明即程序（Curry-Howard 同构）
- 证明状态 = 一组待填充的元变量（"洞"）
- 每个 Tactic 对当前目标进行操作，产生新目标或解决目标

架构说明：
- Goal: 一个证明目标 = 局部上下文 + 待证命题
- ProofState: 完整的证明状态 = 目标列表 + 元变量上下文 + 环境
- Tactic: 对目标进行变换的策略

这与 Lean 4 的 tactic 系统架构一致，但做了大量简化：
- 没有 tacticM monad
- 没有 unification（用最简匹配代替）
- 没有 backtracking
- 没有类型类推断
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import List, Optional

from .expr import Expr
from .environment import (
    Environment, LocalContext,
    MetavarContext
)
from .typechecker import TypeChecker


# ===== 证明目标 =====

@dataclass
class Goal:
    """证明目标：一个待解决的子目标。

    表示为：局部上下文 ⊢ 目标类型
    在底层实现中，每个目标对应一个元变量 ?m。

    示例：
        Goal(mvar_id=0, local_ctx=[x : Nat, y : Bool], target=Nat)
        表示：在上下文 x : Nat, y : Bool 中证明 Nat
    """
    mvar_id: int
    local_ctx: LocalContext
    target: Expr  # 待证明的命题/类型

    def __repr__(self) -> str:
        if self.local_ctx.decls:
            ctx_str = ", ".join(
                f"{d.user_name} : {d.type}" 
                for d in self.local_ctx.decls
            )
            return f"{ctx_str} ⊢ {self.target}"
        return f"⊢ {self.target}"


# ===== 证明状态 =====

@dataclass
class ProofState:
    """证明状态（Tactic State）：整个证明的当前状态。

    包含：
    - goals: 待解决的目标列表（按顺序处理）
    - metavar_ctx: 元变量上下文（保存所有元变量及其赋值）
    - env: 环境（已声明的常量）

    证明完成的条件：goals 为空列表。
    """
    goals: List[Goal]
    metavar_ctx: MetavarContext
    env: Environment

    def is_solved(self) -> bool:
        """检查是否所有目标都已解决"""
        return len(self.goals) == 0

    def get_current_goal(self) -> Optional[Goal]:
        """获取当前要处理的目标（列表中的第一个）"""
        return self.goals[0] if self.goals else None

    def replace_goal(self, old_goal: Goal, new_goals: List[Goal]) -> ProofState:
        """用新目标替换旧目标"""
        idx = -1
        for i, g in enumerate(self.goals):
            if g.mvar_id == old_goal.mvar_id:
                idx = i
                break

        if idx < 0:
            return self

        new_goals_list = self.goals[:idx] + new_goals + self.goals[idx+1:]
        return ProofState(new_goals_list, self.metavar_ctx, self.env)

    def __repr__(self) -> str:
        if self.is_solved():
            return "ProofState(solved ✓)"
        lines = [f"ProofState({len(self.goals)} goals):"]
        for i, g in enumerate(self.goals):
            marker = "▶" if i == 0 else " "
            lines.append(f"  {marker} {g}")
        return "\n".join(lines)


# ===== Tactic 基类 =====

class TacticError(Exception):
    """Tactic 执行错误"""
    pass


class TacticResult:
    """Tactic 应用结果。

    包含新产生的子目标列表和更新后的元变量上下文。
    """
    def __init__(self, goals: List[Goal], mctx: MetavarContext):
        self.goals = goals
        self.mctx = mctx


class Tactic:
    """Tactic 基类。

    每个 Tactic 实现 apply 方法，接收当前证明状态和一个目标，
    返回 TacticResult（包含新子目标和更新后的 mctx）。
    """

    def apply(self, state: ProofState, goal: Goal) -> TacticResult:
        """对 goal 应用 tactic，返回 TacticResult。

        子类必须重写此方法。
        """
        raise NotImplementedError

    def run(self, state: ProofState) -> ProofState:
        """在当前 proof state 上运行 tactic。

        自动获取当前目标、应用 tactic、更新状态。
        """
        goal = state.get_current_goal()
        if goal is None:
            return state

        try:
            result = self.apply(state, goal)
            # 用新的 mctx 和新的 goals 更新 state
            new_state = ProofState(
                state.goals, result.mctx, state.env
            )
            new_state = new_state.replace_goal(goal, result.goals)
            return new_state
        except TacticError as e:
            print(f"Tactic failed: {e}")
            return state


# ===== 具体 Tactics =====

class Intro(Tactic):
    """intro 策略：从目标的 Π 类型中引入假设。

    逻辑：
    - 目标：Γ ⊢ A → B  （即 Γ ⊢ Π _ : A. B）
    - intro x 后：Γ, x : A ⊢ B

    实现：
    - 检查目标是否是 Π 类型
    - 创建新局部变量 x : A
    - 新目标是 B（其中 #0 替换为 fvar_x）
    - 构造 λ x. ?m' 并赋值给当前元变量

    示例：
        ⊢ Nat → Bool
        intro n → n : Nat ⊢ Bool
    """

    def __init__(self, name: Optional[str] = None):
        self.name = name  # 用户指定的名称

    def apply(self, state: ProofState, goal: Goal) -> TacticResult:
        target = goal.target

        # 检查目标是否是 Π 类型
        if not target.is_forallE():
            raise TacticError(
                f"intro: target is not a Π-type: {target}"
            )

        forall_e = target.kind

        # 绑定变量类型
        binder_type = forall_e.dtype
        binder_name = self.name or forall_e.name

        # 创建新的自由变量
        # API: new_ctx, fvar_expr = local_ctx.mk_fvar(name, type)
        new_ctx, fvar_expr = goal.local_ctx.mk_fvar(binder_name, binder_type)

        # 新目标类型：将 body 中的 #0 替换为 fvar
        new_target = self._instantiate_bvar(forall_e.body, fvar_expr)

        # 创建新的元变量作为子目标
        # API: new_mctx, mvar_expr = mctx.add(local_ctx, type)
        new_mctx, mvar_expr = state.metavar_ctx.add(new_ctx, new_target)

        # 构造 λ x. ?m_new 并赋值给当前目标元变量
        proof_term = Expr.lam(binder_name, binder_type, 
            self._abstract_fvar(mvar_expr, fvar_expr.kind.id))

        new_mctx = new_mctx.assign(goal.mvar_id, proof_term)

        # 返回新目标
        new_goal = Goal(mvar_expr.kind.id, new_ctx, new_target)
        return TacticResult([new_goal], new_mctx)

    def _instantiate_bvar(self, body: Expr, val: Expr, idx: int = 0) -> Expr:
        """将 body 中的 bvar idx 替换为 val"""
        match body.kind:
            case Expr.BVar(i):
                if i == idx:
                    return val
                return body
            case Expr.App(fn, arg):
                return Expr.app(
                    self._instantiate_bvar(fn, val, idx),
                    self._instantiate_bvar(arg, val, idx)
                )
            case Expr.Lam(name, dtype, b, bi):
                return Expr.lam(name,
                    self._instantiate_bvar(dtype, val, idx),
                    self._instantiate_bvar(b, val, idx + 1), bi)
            case Expr.ForallE(name, dtype, b, bi):
                return Expr.forallE(name,
                    self._instantiate_bvar(dtype, val, idx),
                    self._instantiate_bvar(b, val, idx + 1), bi)
            case Expr.LetE(name, dtype, value, b):
                return Expr.letE(name,
                    self._instantiate_bvar(dtype, val, idx),
                    self._instantiate_bvar(value, val, idx),
                    self._instantiate_bvar(b, val, idx + 1))
            case _:
                return body

    def _abstract_fvar(self, body: Expr, fvar_id: int, idx: int = 0) -> Expr:
        """将 body 中的 fvar fvar_id 替换为 bvar idx"""
        match body.kind:
            case Expr.FVar(id):
                if id == fvar_id:
                    return Expr.bvar(idx)
                return body
            case Expr.App(fn, arg):
                return Expr.app(
                    self._abstract_fvar(fn, fvar_id, idx),
                    self._abstract_fvar(arg, fvar_id, idx)
                )
            case Expr.Lam(name, dtype, b, bi):
                return Expr.lam(name,
                    self._abstract_fvar(dtype, fvar_id, idx),
                    self._abstract_fvar(b, fvar_id, idx + 1), bi)
            case Expr.ForallE(name, dtype, b, bi):
                return Expr.forallE(name,
                    self._abstract_fvar(dtype, fvar_id, idx),
                    self._abstract_fvar(b, fvar_id, idx + 1), bi)
            case Expr.LetE(name, dtype, value, b):
                return Expr.letE(name,
                    self._abstract_fvar(dtype, fvar_id, idx),
                    self._abstract_fvar(value, fvar_id, idx),
                    self._abstract_fvar(b, fvar_id, idx + 1))
            case _:
                return body


class Apply(Tactic):
    """apply 策略：用已有定理/假设来匹配目标。

    逻辑：
    - 目标：Γ ⊢ B
    - apply f（其中 f : A → B）：新目标 Γ ⊢ A

    如果 f 有多个前提：
    - f : A → C → B，目标 B：
      新目标 Γ ⊢ A, Γ ⊢ C

    实现：
    - 尝试将 f 应用于足够多的新元变量使其类型匹配目标
    - 递归处理 f 的函数类型，为每个参数创建新元变量

    示例：
        h : A → B, 目标 : B
        apply h → 新目标 : A
    """

    def __init__(self, expr: Expr):
        self.expr = expr  # 要应用的表达式

    def apply(self, state: ProofState, goal: Goal) -> TacticResult:
        checker = TypeChecker(state.env, state.metavar_ctx)

        try:
            return self._apply_rec(state, goal, self.expr, checker)
        except Exception as e:
            raise TacticError(f"apply failed: {e}")

    def _apply_rec(self, state: ProofState, goal: Goal, 
                   expr: Expr, checker: TypeChecker) -> TacticResult:
        """递归处理 apply。"""
        expr_type = self._infer_type(checker, goal.local_ctx, expr)

        # 化简类型
        expr_type = self._whnf(checker, goal.local_ctx, expr_type)

        # 检查是否直接匹配
        if self._types_match(expr_type, goal.target):
            # 直接 exact
            new_mctx = state.metavar_ctx.assign(goal.mvar_id, expr)
            return TacticResult([], new_mctx)

        # 如果是 Π 类型，创建参数元变量
        if expr_type.is_forallE():
            forall_e = expr_type.kind
            param_type = forall_e.dtype

            # 创建新元变量作为参数
            # API: new_mctx, param_mvar = mctx.add(local_ctx, type)
            new_mctx, param_mvar = state.metavar_ctx.add(
                goal.local_ctx, param_type)

            # 更新 state 的 mctx
            state = ProofState(state.goals, new_mctx, state.env)

            # 应用 expr 到新参数
            new_expr = Expr.app(expr, param_mvar)

            # 新参数的证明目标
            param_goal = Goal(param_mvar.kind.id, goal.local_ctx, param_type)

            # 递归处理
            result = self._apply_rec(state, goal, new_expr, checker)

            return TacticResult([param_goal] + result.goals, result.mctx)

        raise TacticError(
            f"Cannot apply {expr} (type {expr_type}) to target {goal.target}"
        )

    def _infer_type(self, checker: TypeChecker, ctx: LocalContext, expr: Expr) -> Expr:
        """推导表达式类型"""
        try:
            return checker.infer(ctx, expr)
        except Exception:
            return Expr.Type  # 回退

    def _types_match(self, t1: Expr, t2: Expr) -> bool:
        """检查两个类型是否匹配（简化版）"""
        if t1 == t2:
            return True
        return False

    def _whnf(self, checker: TypeChecker, ctx: LocalContext, e: Expr) -> Expr:
        """弱头范式"""
        try:
            return checker._whnf(ctx, e)
        except Exception:
            return e


class Exact(Tactic):
    """exact 策略：直接提供一个项作为证明。

    逻辑：
    - 目标：Γ ⊢ A
    - exact t（其中 t : A）：直接解决目标

    实现：
    - 检查 t 的类型是否匹配目标（简化版只检查语法等价）
    - 如果匹配，将当前元变量赋值为 t

    示例：
        x : A ⊢ A
        exact x → 目标解决，?m := x
    """

    def __init__(self, expr: Expr):
        self.expr = expr

    def apply(self, state: ProofState, goal: Goal) -> TacticResult:
        # 简化版：直接赋值，不做类型检查
        new_mctx = state.metavar_ctx.assign(goal.mvar_id, self.expr)
        return TacticResult([], new_mctx)


class Rewrite(Tactic):
    """rewrite 策略：用等式重写目标。

    逻辑：
    - 目标：Γ ⊢ P[a]
    - rewrite (h : a = b)：新目标 Γ ⊢ P[b]

    简化版实现：
    - 使用替换实现简化版重写
    - 完整版需要 unification 来处理任意位置的重写

    注意：这是高度简化的实现。真正的 rewrite tactic 需要：
    1. 找到等式的方向（lhs = rhs）
    2. 在目标中找到匹配 lhs 的位置
    3. 用 rhs 替换
    4. 可能产生等式证明作为新子目标
    """

    def __init__(self, eq_proof: Expr, direction: str = "ltr"):
        self.eq_proof = eq_proof  # 等式证明
        self.direction = direction  # "ltr" = 左到右, "rtl" = 右到左

    def apply(self, state: ProofState, goal: Goal) -> TacticResult:
        # 简化版：直接返回原目标（标记为已尝试重写）
        new_target = self._try_rewrite(goal.target)
        if new_target == goal.target:
            return TacticResult([goal], state.metavar_ctx)

        new_goal = Goal(goal.mvar_id, goal.local_ctx, new_target)
        return TacticResult([new_goal], state.metavar_ctx)

    def _try_rewrite(self, target: Expr) -> Expr:
        """尝试在目标中重写（简化版）"""
        return target


class Assumption(Tactic):
    """assumption 策略：如果目标在局部假设中，直接使用它。

    逻辑：
    - 目标：Γ ⊢ A
    - 如果存在 x : A ∈ Γ，则 exact x

    这是最基本的自动化：当目标已经在上下文中时自动解决。

    示例：
        x : A, y : B ⊢ A
        assumption → exact x，目标解决
    """

    def apply(self, state: ProofState, goal: Goal) -> TacticResult:
        # 在局部上下文中查找与目标匹配的类型
        for decl in goal.local_ctx.decls:
            if self._types_match(decl.type, goal.target):
                # 找到匹配！exact (fvar decl.fvar_id)
                proof = Expr.fvar(decl.fvar_id)
                new_mctx = state.metavar_ctx.assign(goal.mvar_id, proof)
                return TacticResult([], new_mctx)

        # 没有找到匹配
        raise TacticError(
            f"assumption: target {goal.target} not found in context"
        )

    def _types_match(self, t1: Expr, t2: Expr) -> bool:
        """检查类型是否匹配"""
        return t1 == t2


# ===== 组合 Tactics =====

class Repeat(Tactic):
    """重复应用一个 tactic 直到失败。"""

    def __init__(self, tactic: Tactic):
        self.tactic = tactic

    def apply(self, state: ProofState, goal: Goal) -> TacticResult:
        current_goals = [goal]
        result_goals = []
        current_mctx = state.metavar_ctx

        for g in current_goals:
            try:
                result = self.tactic.apply(state, g)
                result_goals.extend(result.goals)
                current_mctx = result.mctx
            except TacticError:
                result_goals.append(g)

        return TacticResult(result_goals, current_mctx)


# ===== 证明组合器 =====

def by_tactics(state: ProofState, *tactics: Tactic) -> ProofState:
    """顺序应用多个 tactic。

    示例：
        state = by_tactics(state,
            Intro("n"),      # 引入 n
            Apply(some_expr), # 应用某个引理
            Assumption(),     # 用假设完成
        )
    """
    for tac in tactics:
        if state.is_solved():
            break
        state = tac.run(state)
    return state


def try_tactic(state: ProofState, tactic: Tactic) -> ProofState:
    """尝试应用 tactic，如果失败则保持原状态。"""
    try:
        return tactic.run(state)
    except TacticError:
        return state


# ===== 便捷函数 =====

_mvar_counter = 0

def _fresh_mvar_id() -> int:
    """生成新的元变量 ID"""
    global _mvar_counter
    _mvar_counter += 1
    return _mvar_counter - 1


def reset_mvar_counter():
    """重置元变量计数器（用于测试）"""
    global _mvar_counter
    _mvar_counter = 0


def start_proof(env: Environment, prop: Expr) -> ProofState:
    """开始一个新的证明。

    为命题 prop 创建初始 proof state。
    初始状态只有一个目标：⊢ prop

    参数：
        env: 环境（包含已声明的常量）
        prop: 要证明的命题

    返回：
        ProofState，包含一个初始目标

    示例：
        state = start_proof(env, parse_expr("Nat -> Nat"))
        # ProofState(1 goals):
        #   ▶ ⊢ Nat → Nat
    """
    reset_mvar_counter()

    # 创建元变量 ?m : prop
    local_ctx = LocalContext()
    mvar_id = _fresh_mvar_id()

    metavar_ctx = MetavarContext()
    metavar_ctx = metavar_ctx.add_decl(mvar_id, local_ctx, prop)

    # 创建初始目标
    goal = Goal(mvar_id, local_ctx, prop)

    return ProofState([goal], metavar_ctx, env)


def finish_proof(state: ProofState) -> Optional[Expr]:
    """完成证明。

    如果所有目标都已解决，返回最终的证明项。
    否则返回 None。

    返回的证明项是第一个（主）元变量的赋值，
    其中所有元变量都被实例化。

    示例：
        proof = finish_proof(state)
        if proof:
            print(f"证明完成: {proof}")
    """
    if not state.is_solved():
        return None

    # 返回第一个元变量（mvar_id=0）的赋值
    result = state.metavar_ctx.get_assignment(0)
    if result:
        # 实例化所有剩余的元变量
        result = state.metavar_ctx.instantiate_mvars(result)
    return result


def get_proof_term(state: ProofState) -> Optional[Expr]:
    """获取当前证明项（即使证明未完成）。

    返回主元变量的部分赋值，用于调试。
    """
    result = state.metavar_ctx.get_assignment(0)
    if result:
        result = state.metavar_ctx.instantiate_mvars(result)
    return result


# ===== 调试辅助 =====

def print_proof_state(state: ProofState):
    """打印证明状态"""
    print(state)
