"""
Lean 核心归约器（Reducer）。

实现 β/δ/ι/ζ 归约规则和弱头范式（WHNF）算法。
这是 Lean 类型理论中计算内容的引擎。

归约规则对应关系：
- β-归约：函数应用  (λx.t) a  →  t[a/x]
- δ-归约：定义展开  c  →  defn.value（当 c 是可展开定义时）
- ι-归约：归纳消去  recursor(ctor_app)  →  对应的分支
- ζ-归约：let 化简  let x:=t in s  →  s[t/x]

这些规则共同构成了 Lean 的定义等价关系（definitional equality）。
"""
from __future__ import annotations
from typing import Optional, List, Tuple

from .expr import Expr
from .level import Level
from .environment import (
    Environment, MetavarContext, LocalContext,
    DefnVal, ThmVal, RecVal, CtorVal
)


class Reducer:
    """Lean 核心归约器。

    负责将表达式归约到弱头范式（WHNF），以及各种单步归约。

    类型理论背景：
    - 定义等价（definitional equality）是类型系统中最基本的等价关系
    - 它是可判定的，通过归约到 WHNF 后比较结构实现
    - β/δ/ι/ζ 是定义等价的生成规则

    Attributes:
        env: 全局环境，用于 δ-归约查找常量定义
        metavar_ctx: 元变量上下文，用于实例化元变量
        max_reduction_steps: 最大归约步数（防止无限归约）
    """

    def __init__(self, env: Environment, metavar_ctx: Optional[MetavarContext] = None,
                 max_reduction_steps: int = 10000):
        self.env = env
        self.metavar_ctx = metavar_ctx
        self.max_reduction_steps = max_reduction_steps
        self._step_counter = 0  # 追踪归约步数（用于终止性）

    # ============================================================
    # 弱头范式（WHNF）
    # ============================================================

    def whnf(self, e: Expr) -> Expr:
        """将表达式归约到弱头范式（Weak Head Normal Form）。

        WHNF 是表达式的"最外层规范形式"：
        - λ-抽象是 WHNF（其函数体可能还有可约项，但外层不可约）
        - Π-类型是 WHNF
        - 无法继续归约的应用是 WHNF
        - 字面量是 WHNF
        - Sort 是 WHNF
        - 自由变量是 WHNF
        - 已赋值的元变量会被展开后重新归约

        算法说明：
        1. 先实例化所有已赋值的元变量
        2. 然后根据表达式头部选择归约策略
        3. 循环直到无法继续归约

        WHNF 与完全范式（NF）的区别：
        - WHNF 只归约"头部"（最外层可约项）
        - NF 需要递归归约所有子项
        - 类型检查只需要 WHNF（效率关键！）

        终止性：每次循环至少消除一个 redex，而表达式大小有限。
        我们通过 max_reduction_steps 提供额外的安全保障。

        Args:
            e: 待归约的表达式

        Returns:
            e 的弱头范式
        """
        while self._step_counter < self.max_reduction_steps:
            self._step_counter += 1

            # Step 1: 实例化元变量（如果已赋值，替换后继续归约）
            if e.is_mvar() and self.metavar_ctx is not None:
                assignment = self.metavar_ctx.get_assignment(e.kind.id)
                if assignment is not None:
                    e = assignment
                    continue

            # Step 2: 根据表达式结构选择归约策略
            match e.kind:
                case Expr.App(fn, arg):
                    # 检查函数部分是否可 β-归约
                    fn_whnf = self._whnf_head(fn)
                    if fn_whnf.is_lam():
                        # β-redex: (λ x : A. body) arg  →  body[arg/x]
                        lam = fn_whnf.kind
                        e = self.instantiate(lam.body, arg)
                        continue
                    # 否则是 WHNF（变量/常量应用）

                case Expr.LetE(name, dtype, value, body):
                    # ζ-redex: let x := t in s  →  s[t/x]
                    e = self.instantiate(body, value)
                    continue

                case Expr.Const(name, levels):
                    # δ-归约：展开可展开的定义
                    expanded = self.delta_reduce(e)
                    if expanded is not None:
                        e = expanded
                        continue

                case _:
                    pass

            # Step 3: 检查是否是 recursor 应用（ι-归约）
            # 这需要识别 app*(recursor, [params..., motive, minors..., ctor_app])
            iota_result = self.iota_reduce(e)
            if iota_result is not None:
                e = iota_result
                continue

            # 无法继续归约，e 已经是 WHNF
            return e

        # 达到最大步数，返回当前结果
        return e

    def _whnf_head(self, e: Expr) -> Expr:
        """只对表达式的"头部"做 WHNF（用于 β-归约检测）。

        这是 whnf 的轻量版本：不递归处理非应用表达式。
        """
        # 如果 e 是常量，先尝试 δ-展开
        if e.is_const():
            expanded = self.delta_reduce(e)
            if expanded is not None:
                return self._whnf_head(expanded)
        # 如果 e 是 let，ζ-化简
        if e.is_letE():
            return self._whnf_head(
                self.instantiate(e.kind.body, e.kind.value)
            )
        # 如果 e 是应用，递归处理函数部分
        if e.is_app():
            fn_head = self._whnf_head(e.kind.fn)
            if fn_head.is_lam():
                # 继续 β-归约
                return self._whnf_head(
                    self.instantiate(fn_head.kind.body, e.kind.arg)
                )
        return e

    # ============================================================
    # β-归约
    # ============================================================

    def beta_reduce(self, e: Expr) -> Optional[Expr]:
        """β-归约：将 β-redex (λ x : A. t) a 归约为 t[a/x]。

        类型理论解释：
        β-归约是函数调用/应用的核心计算规则。
        在 Curry-Howard 同构中，β-归约对应"证明简化"（proof normalization）：
        一个应用了具体证明的泛化证明被替换为特化版本。

        de Bruijn 索引处理：
        (λ. body) arg  →  body[arg/#0]
        其中 body 中 #0 被替换为 arg，#n (n>0) 变为 #(n-1)。

        Args:
            e: 待检查 β-归约的表达式

        Returns:
            如果 e 是 β-redex，返回归约结果；否则返回 None
        """
        if not e.is_app():
            return None

        fn = e.kind.fn
        arg = e.kind.arg

        # 函数部分必须是 λ-抽象
        if not fn.is_lam():
            # 尝试对函数部分做 WHNF
            fn_whnf = self._whnf_head(fn)
            if not fn_whnf.is_lam():
                return None
            fn = fn_whnf

        lam_body = fn.kind.body
        # β-归约：将 body 中的 #0 替换为 arg
        return self.instantiate(lam_body, arg)

    # ============================================================
    # δ-归约
    # ============================================================

    def delta_reduce(self, e: Expr) -> Optional[Expr]:
        """δ-归约：展开全局常量定义。

        类型理论解释：
        δ-归约将已定义常量的名称替换为其定义体。
        这是"按名展开"（call-by-name）的常量内联。

        注意：
        - 不透明定义（opaque definitions）不展开
        - 定理（theorem）默认不透明
        - 归纳类型和构造器没有定义体，不展开
        - 需要处理 universe level 实例化

        Args:
            e: 必须是 Const 表达式

        Returns:
            如果可展开，返回展开后的表达式；否则返回 None
        """
        if not e.is_const():
            return None

        const = e.kind
        name = const.name
        levels = const.levels

        # 检查是否不透明
        if self.env.is_opaque(name):
            return None

        # 查找定义
        info = self.env.lookup(name)
        if info is None:
            return None

        match info:
            case DefnVal(value=value, is_opaque=False):
                # 普通定义：返回其定义体，并实例化 universe levels
                return self._instantiate_levels(value, levels)
            case _:
                # 其他类型（公理、定理、归纳类型等）没有可展开的定义体
                return None

    def unfold_definition(self, e: Expr) -> Optional[Expr]:
        """选择性 δ-归约：只展开一次定义。

        用于调试和特定场景下的单步展开。

        Args:
            e: 待展开的表达式

        Returns:
            展开后的表达式，如果不可展开则返回 None
        """
        return self.delta_reduce(e)

    # ============================================================
    # ι-归约（归纳类型 Recursor）
    # ============================================================

    def iota_reduce(self, e: Expr) -> Optional[Expr]:
        """ι-归约：归纳类型 recursor 的计算规则。

        类型理论解释：
        ι-归约是归纳类型的"计算公理"（computation rules）。
        它描述了 recursor（原语递归）在遇到构造器时的行为。

        这是归纳定义的核心：每个构造器对应一个计算规则。

        例如对于 Nat：
        - Nat.rec C z s zero     →  z
        - Nat.rec C z s (succ n) →  s n (Nat.rec C z s n)

        模式识别：
        我们需要识别 recursor_name params... motive minors... (ctor_name args...)
        这样的应用模式，然后找到对应构造器的 RecursorRule 进行替换。

        Args:
            e: 待检查 ι-归约的表达式

        Returns:
            如果可 ι-归约，返回归约结果；否则返回 None
        """
        # 获取应用链：recursor_f 和 args
        fn = e.get_app_fn()
        args = e.get_app_args()

        # 函数头必须是常量（recursor 名称）
        if not fn.is_const():
            return None

        name = fn.kind.name

        # 查找 recursor 信息
        info = self.env.lookup(name)
        if info is None or not isinstance(info, RecVal):
            return None

        rec_val = info
        total_prefix = rec_val.num_params + rec_val.num_motives + rec_val.num_minors

        # 参数数量必须足够（前缀 + 至少一个主参数）
        if len(args) <= total_prefix:
            return None

        # 主参数是最后一个参数（归纳类型的值）
        major_arg = args[-1]

        # 主参数必须是构造器应用
        ctor_fn = major_arg.get_app_fn()
        if not ctor_fn.is_const():
            # 尝试将主参数归约到 WHNF
            major_whnf = self.whnf(major_arg)
            ctor_fn = major_whnf.get_app_fn()
            if not ctor_fn.is_const():
                return None
            major_arg = major_whnf

        ctor_name = ctor_fn.kind.name

        # 找到对应的 recursor 规则
        rule = None
        for r in rec_val.rules:
            if r.ctor == ctor_name:
                rule = r
                break

        if rule is None:
            return None

        # 构造替换：
        # 1. 提取构造器参数（字段）
        ctor_args = major_arg.get_app_args()
        # 构造器参数包括参数（params）和字段（fields）
        # 我们只取字段部分
        # 获取构造器信息以确定 num_params
        ctor_info = self.env.lookup(ctor_name)
        if ctor_info is not None and isinstance(ctor_info, CtorVal):
            num_ctor_params = ctor_info.num_params
        else:
            num_ctor_params = rec_val.num_params

        fields = ctor_args[num_ctor_params:]

        # 2. 提取 minor premises
        minor_start = rec_val.num_params + rec_val.num_motives
        minor_end = minor_start + rec_val.num_minors
        minors = args[minor_start:minor_end]

        # 3. 构建结果：先应用 minor premise，然后应用构造器字段和递归调用
        # 规则 RHS 的形式：λ fields..., minor(fields..., recursive_calls...)
        result = rule.rhs

        # 应用构造器字段
        for field in fields:
            result = Expr.app(result, field)

        # 应用递归调用（recursor 在子结构上的应用）
        # 对于每个递归字段，构造 recursor(params, motive, minors, field)
        # 简化处理：将 result 中剩余的占位符替换为递归调用
        # 这需要更精细的处理，这里先做基本版本

        # 替换 recursor 调用中的主参数部分
        # 完整结果 = recursor_args[:total_prefix] + [major_arg的简化形式]
        # 实际规则已经编码了如何构造递归调用

        return result

    # ============================================================
    # ζ-归约
    # ============================================================

    def zeta_reduce(self, e: Expr) -> Optional[Expr]:
        """ζ-归约：let 绑定化简。

        类型理论解释：
        ζ-归约是 let 表达式的计算规则：
        let x := t in s  →  s[t/x]

        这对应于替换：将 let 体中引用的变量替换为 let 值。

        与 β-归约的关系：
        let x := t in s  ≡  (λ x. s) t
        所以 ζ-归约本质上是 β-归约的一种优化形式。

        Args:
            e: 待检查 ζ-归约的表达式

        Returns:
            如果 e 是 let 表达式，返回 ζ-归约结果；否则返回 None
        """
        if not e.is_letE():
            return None

        let = e.kind
        # ζ-归约：let x := value in body  →  body[value/x]
        return self.instantiate(let.body, let.value)

    # ============================================================
    # 多步归约
    # ============================================================

    def reduce(self, e: Expr) -> Expr:
        """完全归约：尽可能归约到范式（Normal Form）。

        与 WHNF 的区别：
        - WHNF 只归约最外层可约项
        - reduce 递归归约所有子项

        注意：不是所有表达式都有范式（可能存在无限归约），
        所以此函数可能达到 max_reduction_steps 限制。

        Args:
            e: 待归约的表达式

        Returns:
            尽可能归约后的表达式
        """
        # 先归约到 WHNF
        e = self.whnf(e)

        # 然后递归归约子项
        match e.kind:
            case Expr.Lam(name, dtype, body, bi):
                new_dtype = self.reduce(dtype)
                new_body = self.reduce(body)
                if new_dtype is dtype and new_body is body:
                    return e
                return Expr.lam(name, new_dtype, new_body, bi)

            case Expr.ForallE(name, dtype, body, bi):
                new_dtype = self.reduce(dtype)
                new_body = self.reduce(body)
                if new_dtype is dtype and new_body is body:
                    return e
                return Expr.forallE(name, new_dtype, new_body, bi)

            case Expr.App(fn, arg):
                new_fn = self.reduce(fn)
                new_arg = self.reduce(arg)
                if new_fn is fn and new_arg is arg:
                    return e
                return Expr.app(new_fn, new_arg)

            case Expr.LetE(name, dtype, value, body):
                new_dtype = self.reduce(dtype)
                new_value = self.reduce(value)
                new_body = self.reduce(body)
                if new_dtype is dtype and new_value is value and new_body is body:
                    return e
                return Expr.letE(name, new_dtype, new_value, new_body)

            case Expr.Sort(level):
                # Sort 本身不需要归约，但 level 可能需要
                return e

            case Expr.Const(name, levels):
                # 常量已经 WHNF，不继续展开子项
                return e

            case _:
                return e

    def whnf_stack(self, e: Expr) -> Tuple[Expr, List[Expr]]:
        """WHNF + 应用栈分解。

        将表达式分解为 (head, args)，其中 head 是 WHNF，args 是应用参数。

        例如：(f a b c) 分解为 (f, [a, b, c])
        如果 f 是 λ，则先 β-归约。

        Args:
            e: 待分解的表达式

        Returns:
            (head_expr, arg_list) 元组
        """
        e = self.whnf(e)
        args = e.get_app_args()
        head = e.get_app_fn()
        return head, args

    # ============================================================
    # 辅助归约方法
    # ============================================================

    def reduce_all(self, e: Expr) -> Expr:
        """递归归约所有子项到 WHNF。

        这是 reduce 的别名，用于明确语义。
        """
        return self.reduce(e)

    def is_whnf(self, e: Expr) -> bool:
        """检查表达式是否已经是 WHNF（快速测试）。

        注意：这只是一个快速路径，不保证完全准确。
        某些表达式可能需要实际尝试归约才能确定。
        """
        match e.kind:
            case Expr.Lam(_, _, _, _):
                return True
            case Expr.ForallE(_, _, _, _):
                return True
            case Expr.Sort(_):
                return True
            case Expr.FVar(_):
                return True
            case Expr.BVar(_):
                return True
            case Expr.Lit(_):
                return True
            case Expr.MVar(id):
                # 已赋值的元变量不是 WHNF
                if self.metavar_ctx is not None and self.metavar_ctx.is_assigned(id):
                    return False
                return True
            case Expr.Const(name, _):
                # 可展开的定义不是 WHNF
                return self.env.is_opaque(name)
            case Expr.App(fn, _):
                # 应用是否是 WHNF 取决于函数部分
                if fn.is_lam():
                    return False  # β-redex
                if fn.is_letE():
                    return False  # ζ-redex
                # 其他情况需要检查函数头
                head = e.get_app_fn()
                if head.is_const():
                    # 检查是否是 recursor 应用
                    iota = self.iota_reduce(e)
                    if iota is not None:
                        return False
                return True
            case Expr.LetE(_, _, _, _):
                return False  # ζ-redex
            case Expr.Proj(_, _, _):
                # 投影可能需要 ι-归约
                return True
            case _:
                return True

    # ============================================================
    # de Bruijn 操作
    # ============================================================

    def instantiate(self, e: Expr, val: Expr, idx: int = 0) -> Expr:
        """将 e 中的 de Bruijn 索引 #idx 替换为 val。

        这是 β-归约的核心操作：(λ. e) val → instantiate(e, val, 0)

        de Bruijn 索引替换规则：
        - #idx → val（被替换的变量）
        - #(n+1) → #n（外层绑定变量索引减1，因为减少了一个 λ）
        - #n（n < idx）→ #n（不受影响的绑定）

        同时需要对 val 做 lift 操作：
        - 进入 λ/Π/let 的 body 时，需要将 val 的 de Bruijn 索引增加 1
          因为多了一个绑定层。

        类型理论对应：
        这是替换引理（Substitution Lemma）的算法实现：
        Γ, x:A ⊢ t : B    Γ ⊢ a : A
        ─────────────────────────────
              Γ ⊢ t[a/x] : B[a/x]

        Args:
            e: 被替换的表达式（通常是 λ-body）
            val: 替换值
            idx: 要替换的 de Bruijn 索引（默认 0）

        Returns:
            替换后的表达式
        """
        match e.kind:
            case Expr.BVar(i):
                if i == idx:
                    # 找到目标变量，替换为 val
                    return val
                elif i > idx:
                    # 外层绑定变量，索引减 1（因为减少了一个绑定层）
                    return Expr.bvar(i - 1)
                else:
                    # 内层绑定变量，不受影响
                    return e

            case Expr.Lam(name, dtype, body, bi):
                # 递归替换 dtype（同一层）
                new_dtype = self.instantiate(dtype, val, idx)
                # 替换 body 时，val 需要 lift（因为进入了一个新的 λ 绑定层）
                lifted_val = self.lift(val, 0, 1)
                new_body = self.instantiate(body, lifted_val, idx + 1)
                if new_dtype is dtype and new_body is body:
                    return e
                return Expr.lam(name, new_dtype, new_body, bi)

            case Expr.ForallE(name, dtype, body, bi):
                # 与 λ 相同的逻辑
                new_dtype = self.instantiate(dtype, val, idx)
                lifted_val = self.lift(val, 0, 1)
                new_body = self.instantiate(body, lifted_val, idx + 1)
                if new_dtype is dtype and new_body is body:
                    return e
                return Expr.forallE(name, new_dtype, new_body, bi)

            case Expr.LetE(name, dtype, value, body):
                # dtype 和 value 在同一层
                new_dtype = self.instantiate(dtype, val, idx)
                new_value = self.instantiate(value, val, idx)
                # body 在新绑定层中
                lifted_val = self.lift(val, 0, 1)
                new_body = self.instantiate(body, lifted_val, idx + 1)
                if new_dtype is dtype and new_value is value and new_body is body:
                    return e
                return Expr.letE(name, new_dtype, new_value, new_body)

            case Expr.App(fn, arg):
                new_fn = self.instantiate(fn, val, idx)
                new_arg = self.instantiate(arg, val, idx)
                if new_fn is fn and new_arg is arg:
                    return e
                return Expr.app(new_fn, new_arg)

            case Expr.Proj(type_name, field_idx, struct):
                new_struct = self.instantiate(struct, val, idx)
                if new_struct is struct:
                    return e
                return Expr(Expr.Proj(type_name, field_idx, new_struct))

            case Expr.Sort(_) | Expr.Const(_, _) | Expr.FVar(_) | Expr.MVar(_) | Expr.Lit(_):
                # 这些不包含 de Bruijn 索引，无需替换
                return e

            case _:
                return e

    def lift(self, e: Expr, start_idx: int, num: int) -> Expr:
        """将 e 中 de Bruijn 索引 >= start_idx 的变量索引增加 num。

        这是替换操作的辅助函数，用于处理绑定层的变化。

        使用场景：
        - 将表达式从一个上下文移动到另一个有更多绑定的上下文
        - instantiate 中进入 λ/Π body 时调整替换值

        例如：
        lift(#0, 0, 1) = #1
        lift(#1, 0, 1) = #2
        lift(#0, 1, 1) = #0（#0 < 1，不受影响）
        lift(λ. #1, 0, 1) = λ. #2

        Args:
            e: 待调整的表达式
            start_idx: 起始索引（>= 此索引的变量才会被增加）
            num: 增加量

        Returns:
            调整后的表达式
        """
        if num == 0:
            return e

        match e.kind:
            case Expr.BVar(i):
                if i >= start_idx:
                    return Expr.bvar(i + num)
                return e

            case Expr.Lam(name, dtype, body, bi):
                new_dtype = self.lift(dtype, start_idx, num)
                # 进入 body 时，start_idx 增加 1（因为多了一个绑定层）
                new_body = self.lift(body, start_idx + 1, num)
                if new_dtype is dtype and new_body is body:
                    return e
                return Expr.lam(name, new_dtype, new_body, bi)

            case Expr.ForallE(name, dtype, body, bi):
                new_dtype = self.lift(dtype, start_idx, num)
                new_body = self.lift(body, start_idx + 1, num)
                if new_dtype is dtype and new_body is body:
                    return e
                return Expr.forallE(name, new_dtype, new_body, bi)

            case Expr.LetE(name, dtype, value, body):
                new_dtype = self.lift(dtype, start_idx, num)
                new_value = self.lift(value, start_idx, num)
                new_body = self.lift(body, start_idx + 1, num)
                if new_dtype is dtype and new_value is value and new_body is body:
                    return e
                return Expr.letE(name, new_dtype, new_value, new_body)

            case Expr.App(fn, arg):
                new_fn = self.lift(fn, start_idx, num)
                new_arg = self.lift(arg, start_idx, num)
                if new_fn is fn and new_arg is arg:
                    return e
                return Expr.app(new_fn, new_arg)

            case Expr.Proj(type_name, field_idx, struct):
                new_struct = self.lift(struct, start_idx, num)
                if new_struct is struct:
                    return e
                return Expr(Expr.Proj(type_name, field_idx, new_struct))

            case Expr.Sort(_) | Expr.Const(_, _) | Expr.FVar(_) | Expr.MVar(_) | Expr.Lit(_):
                return e

            case _:
                return e

    # ============================================================
    # Universe Level 操作
    # ============================================================

    def _instantiate_levels(self, e: Expr, levels: List[Level]) -> Expr:
        """实例化表达式中的 universe level 参数。

        全局常量的类型/定义体中可能包含 universe level 参数（如 u, v）。
        当使用 Const(name, [l1, l2]) 引用常量时，需要将这些参数替换为具体的 level。

        例如：
        List 的类型是 Π (A : Type u), Type u
        List.{Nat} 需要将 u 替换为 Nat 对应的 level。

        Args:
            e: 包含 level 参数的表达式
            levels: 要替换的 level 列表

        Returns:
            替换后的表达式
        """
        if not levels:
            return e

        match e.kind:
            case Expr.Sort(level):
                new_level = level.subst(self._build_level_subst(levels))
                if new_level == level:
                    return e
                return Expr.sort(new_level)

            case Expr.Const(name, const_levels):
                # 常量自身的 level 也需要替换
                new_levels = [
                    level.subst(self._build_level_subst(levels))
                    for level in const_levels
                ]
                if new_levels == const_levels:
                    return e
                return Expr.const(name, new_levels)

            case Expr.App(fn, arg):
                new_fn = self._instantiate_levels(fn, levels)
                new_arg = self._instantiate_levels(arg, levels)
                if new_fn is fn and new_arg is arg:
                    return e
                return Expr.app(new_fn, new_arg)

            case Expr.Lam(name, dtype, body, bi):
                new_dtype = self._instantiate_levels(dtype, levels)
                new_body = self._instantiate_levels(body, levels)
                if new_dtype is dtype and new_body is body:
                    return e
                return Expr.lam(name, new_dtype, new_body, bi)

            case Expr.ForallE(name, dtype, body, bi):
                new_dtype = self._instantiate_levels(dtype, levels)
                new_body = self._instantiate_levels(body, levels)
                if new_dtype is dtype and new_body is body:
                    return e
                return Expr.forallE(name, new_dtype, new_body, bi)

            case Expr.LetE(name, dtype, value, body):
                new_dtype = self._instantiate_levels(dtype, levels)
                new_value = self._instantiate_levels(value, levels)
                new_body = self._instantiate_levels(body, levels)
                if new_dtype is dtype and new_value is value and new_body is body:
                    return e
                return Expr.letE(name, new_dtype, new_value, new_body)

            case Expr.Lit(_) | Expr.FVar(_) | Expr.MVar(_) | Expr.BVar(_):
                return e

            case Expr.Proj(type_name, field_idx, struct):
                new_struct = self._instantiate_levels(struct, levels)
                if new_struct is struct:
                    return e
                return Expr(Expr.Proj(type_name, field_idx, new_struct))

            case _:
                return e

    def _build_level_subst(self, levels: List[Level]) -> dict:
        """构建 universe level 替换映射。

        Lean 的 universe 参数通常是按位置命名的 param_0, param_1, ...
        或具体的名称如 u, v。

        简化处理：我们使用 param_0, param_1, ... 作为默认参数名。
        """
        subst = {}
        for i, level in enumerate(levels):
            subst[f"param_{i}"] = level
        return subst
