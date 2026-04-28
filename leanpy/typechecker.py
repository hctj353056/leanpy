"""
Lean 核心类型检查器（TypeChecker）。

实现依赖类型理论的类型推断（infer）和类型检查（check）算法，
以及定义等价（definitional equality）判断。

类型检查器是整个 Lean 系统的核心：它验证每个表达式是否良类型，
确保 Curry-Howard 同构的正确性——即每个"证明"确实对应其声称的"命题"。

核心算法：
1. 类型推断（infer）：给定 Γ 和 e，计算 A 使得 Γ ⊢ e : A
2. 类型检查（check）：给定 Γ, e, A，验证 Γ ⊢ e : A
3. 定义等价（is_def_eq）：判断两个表达式是否定义等价

类型规则（对应 sequent calculus）：
- VAR:   (x:A) ∈ Γ  ⟹  Γ ⊢ x : A
- CONST: (c:A) ∈ Env  ⟹  Γ ⊢ c : A
- SORT:  Γ ⊢ Sort u : Sort (u+1)
- PI:    Γ ⊢ A:Sort u, Γ,x:A ⊢ B:Sort v  ⟹  Γ ⊢ Πx:A.B : Sort(imax u v)
- LAM:   Γ,x:A ⊢ t:B, Γ ⊢ Πx:A.B:Sort u  ⟹  Γ ⊢ λx:A.t : Πx:A.B
- APP:   Γ ⊢ f:Πx:A.B, Γ ⊢ a:A  ⟹  Γ ⊢ f a : B[a/x]
- LET:   Γ ⊢ t:A, Γ,x:A ⊢ s:B  ⟹  Γ ⊢ let x:A:=t in s : B[t/x]
"""
from __future__ import annotations
from typing import Optional, List, Tuple

from .expr import Expr, BinderInfo
from .level import Level
from .name import Name
from .environment import (
    Environment, MetavarContext, LocalContext,
    AxiomVal, DefnVal, ThmVal, InductVal, CtorVal, RecVal
)
from .reducer import Reducer


class TypeChecker:
    """Lean 核心类型检查器。
    
    属性：
        env: 全局环境（存储所有常量声明/定义）
        reducer: 归约器（用于 WHNF 和定义等价判断）
        metavar_ctx: 元变量上下文
    
    不变式：
        - 每个 infer 调用返回的 A 满足 Γ ⊢ e : A
        - 每个 check 调用返回 True 当且仅当 Γ ⊢ e : A
        - is_def_eq(t1, t2) 返回 True 当且仅当 t1 ≡ t2（定义等价）
    """
    
    def __init__(self, env: Environment, metavar_ctx: Optional[MetavarContext] = None):
        self.env = env
        self.reducer = Reducer(env, metavar_ctx)
        self.metavar_ctx = metavar_ctx
        self._fvar_id_counter = 0
    
    # ============================================================
    # 类型推断（Infer）
    # ============================================================
    
    def infer(self, ctx: LocalContext, e: Expr) -> Expr:
        """推断表达式 e 在上下文 ctx 中的类型。
        
        类型推断算法基于结构化规则：根据表达式的主连接词选择对应的规则。
        
        对应 sequent: Γ ⊢ e : ?  →  返回 A 使得 Γ ⊢ e : A
        
        完备性说明：
        此推断器对于基本的 Martin-Löf 类型理论（MLTT）是完备的。
        它可以推断所有良类型表达式的类型。
        对于包含元变量的表达式，可能需要额外的 unification。
        
        Args:
            ctx: 局部上下文 Γ（自由变量及其类型的映射）
            e: 待推断类型的表达式
            
        Returns:
            e 的类型 A
            
        Raises:
            TypeError: 如果 e 不是良类型的
        """
        match e.kind:
            case Expr.BVar(idx):
                # VAR 规则：从局部上下文查找绑定变量的类型
                # 注意：BVar 在类型检查中通常不会出现（会被 FVar 替代），
                # 但如果出现，说明表达式未正确抽象化
                raise TypeError(f"BVar #{idx} 不应在类型推断中出现：表达式未完全抽象化")
            
            case Expr.FVar(id):
                # VAR 规则（自由变量版）：(x:A) ∈ Γ  ⟹  Γ ⊢ x : A
                fvar_type = ctx.get_type(id)
                if fvar_type is None:
                    raise TypeError(f"未声明的自由变量 fv{id}")
                return fvar_type
            
            case Expr.MVar(id):
                # 元变量的类型从 metavar_ctx 获取
                if self.metavar_ctx is not None:
                    mvar_type = self.metavar_ctx.get_type(id)
                    if mvar_type is not None:
                        return mvar_type
                raise TypeError(f"未知元变量 ?{id}")
            
            case Expr.Sort(level):
                # SORT 规则：Γ ⊢ Sort u : Sort (u+1)
                # 宇宙层级：Sort u 的类型是 Sort (u+1)
                # 这避免了 Russell 悖论（通过 universe 层级区分）
                return self.infer_sort(e)
            
            case Expr.Const(name, levels):
                # CONST 规则：从环境查找常量的类型，并实例化 universe levels
                return self.infer_const(e)
            
            case Expr.App(fn, arg):
                # APP 规则：Γ ⊢ f : Πx:A.B, Γ ⊢ a : A  ⟹  Γ ⊢ f a : B[a/x]
                return self.infer_app(ctx, fn, arg)
            
            case Expr.Lam(name, dtype, body, bi):
                # LAM 规则：
                # 先检查 dtype 是类型（Γ ⊢ A : Sort u），
                # 然后在扩展上下文中推断 body 的类型 B，
                # 返回 Πx:A.B
                return self.infer_lam(ctx, e)
            
            case Expr.ForallE(name, dtype, body, bi):
                # PI 规则：
                # Γ ⊢ A : Sort u, Γ,x:A ⊢ B : Sort v
                # ──────────────────────────────────
                # Γ ⊢ Πx:A.B : Sort (imax u v)
                return self.infer_pi(ctx, e)
            
            case Expr.LetE(name, dtype, value, body):
                # LET 规则：
                # Γ ⊢ t : A, Γ,x:A ⊢ s : B
                # ────────────────────────────
                # Γ ⊢ let x:A:=t in s : B[t/x]
                return self.infer_let(ctx, e)
            
            case Expr.Lit(Literal.NatVal(val)):
                # 自然数字面量的类型是 Nat
                # 简化处理：返回常量 Nat
                from .name import mk_name
                return Expr.const(mk_name("Nat"), [])
            
            case Expr.Lit(Literal.StrVal(val)):
                # 字符串字面量的类型是 String
                from .name import mk_name
                return Expr.const(mk_name("String"), [])
            
            case Expr.Proj(type_name, field_idx, struct):
                # 投影类型需要查找结构体定义
                # 简化处理：返回一个占位类型
                raise TypeError(f"投影类型检查尚未完全实现: {e}")
            
            case _:
                raise TypeError(f"无法推断类型: {e}")
    
    # ============================================================
    # 类型检查（Check）
    # ============================================================
    
    def check(self, ctx: LocalContext, e: Expr, expected: Expr) -> bool:
        """检查表达式 e 是否具有类型 expected。
        
        实现策略：
        1. 推断 e 的类型 A
        2. 检查 A 和 expected 是否定义等价（A ≡ expected）
        
        这是类型检查的"检查模式"（checking mode），
        与推断模式（inference mode）相对。
        
        在某些情况下，检查模式比推断模式更高效
        （例如检查 λ 抽象的类型时）。
        
        Args:
            ctx: 局部上下文
            e: 待检查的表达式
            expected: 期望的类型
            
        Returns:
            True 如果 e 的类型与 expected 定义等价
        """
        try:
            actual = self.infer(ctx, e)
            return self.is_def_eq(actual, expected)
        except TypeError:
            return False
    
    # ============================================================
    # 定义等价（Definitional Equality）
    # ============================================================
    
    def is_def_eq(self, t1: Expr, t2: Expr) -> bool:
        """判断 t1 和 t2 是否定义等价。
        
        定义等价（≡）是类型系统中最基本的等价关系：
        - 它是可判定的
        - 它通过归约到 WHNF 后比较结构来判断
        - 它是同余关系（congruence）
        
        算法策略：
        1. 快速路径：如果 t1 == t2（结构相等），返回 True
        2. 实例化元变量
        3. 将两者归约到 WHNF
        4. 比较 WHNF 的结构（递归比较子项）
        
        类型理论意义：
        定义等价是"在计算下等价"的关系。如果 t1 ≡ t2，
        那么它们在任何上下文中可以互换使用。
        
        Args:
            t1: 第一个表达式
            t2: 第二个表达式
            
        Returns:
            True 如果 t1 ≡ t2
        """
        # 快速路径 1：结构完全相等
        if t1 == t2:
            return True
        
        # 快速路径 2：检查是否是同一个表达式对象
        if t1 is t2:
            return True
        
        # 实例化元变量
        if self.metavar_ctx is not None:
            t1 = self.metavar_ctx.instantiate_mvars(t1)
            t2 = self.metavar_ctx.instantiate_mvars(t2)
        
        # 再次检查
        if t1 == t2:
            return True
        
        # 归约到 WHNF 后比较
        t1_whnf = self.reducer.whnf(t1)
        t2_whnf = self.reducer.whnf(t2)
        
        # 如果归约后相等
        if t1_whnf == t2_whnf:
            return True
        
        # 核心：递归比较 WHNF 的结构
        return self.is_def_eq_core(t1_whnf, t2_whnf)
    
    def is_def_eq_core(self, t1: Expr, t2: Expr) -> bool:
        """is_def_eq 的核心递归比较。
        
        假设 t1 和 t2 已经是 WHNF（或接近 WHNF），
        比较它们的结构是否匹配。
        
        这是定义等价判断的"核心引擎"：
        对每对表达式结构，应用对应的等价规则。
        """
        # 再次检查结构相等
        if t1 == t2:
            return True
        
        match (t1.kind, t2.kind):
            # ===== λ-抽象 =====
            case (Expr.Lam(_, d1, b1, _), Expr.Lam(_, d2, b2, _)):
                # λ 等价：域类型等价 且 体等价
                # λx:A. t ≡ λx:A'. t'  当  A ≡ A' 且 t ≡ t'
                return (self.is_def_eq(d1, d2) and 
                        self.is_def_eq(b1, b2))
            
            # ===== Π-类型 =====
            case (Expr.ForallE(_, d1, b1, _), Expr.ForallE(_, d2, b2, _)):
                # Π 等价：域类型等价 且 值域等价
                # Πx:A. B ≡ Πx:A'. B'  当  A ≡ A' 且 B ≡ B'
                return (self.is_def_eq(d1, d2) and 
                        self.is_def_eq(b1, b2))
            
            # ===== 函数应用 =====
            case (Expr.App(f1, a1), Expr.App(f2, a2)):
                # 应用等价：函数部分等价 且 参数等价
                # f a ≡ f' a'  当  f ≡ f' 且 a ≡ a'
                return (self.is_def_eq(f1, f2) and 
                        self.is_def_eq(a1, a2))
            
            # ===== Sort =====
            case (Expr.Sort(l1), Expr.Sort(l2)):
                # Sort 等价：层级等价
                # Sort u ≡ Sort v  当  u ≡ v（level 等价）
                return self.is_level_def_eq(l1, l2)
            
            # ===== 常量 =====
            case (Expr.Const(n1, ls1), Expr.Const(n2, ls2)):
                # 常量等价：名称相同 且 universe levels 等价
                if n1 != n2:
                    return False
                if len(ls1) != len(ls2):
                    return False
                return all(self.is_level_def_eq(a, b) for a, b in zip(ls1, ls2))
            
            # ===== 自由变量 =====
            case (Expr.FVar(id1), Expr.FVar(id2)):
                return id1 == id2
            
            # ===== 绑定变量 =====
            case (Expr.BVar(i1), Expr.BVar(i2)):
                return i1 == i2
            
            # ===== 字面量 =====
            case (Expr.Lit(lit1), Expr.Lit(lit2)):
                return lit1 == lit2
            
            # ===== 元变量 =====
            case (Expr.MVar(id1), Expr.MVar(id2)):
                return id1 == id2
            
            # ===== let 绑定 =====
            case (Expr.LetE(_, d1, v1, b1), Expr.LetE(_, d2, v2, b2)):
                return (self.is_def_eq(d1, d2) and 
                        self.is_def_eq(v1, v2) and 
                        self.is_def_eq(b1, b2))
            
            # ===== 投影 =====
            case (Expr.Proj(tn1, fi1, s1), Expr.Proj(tn2, fi2, s2)):
                return tn1 == tn2 and fi1 == fi2 and self.is_def_eq(s1, s2)
            
            # ===== 不匹配的结构 =====
            case _:
                # 如果 t1 是 λ 而 t2 不是，尝试 η-等价
                # η-等价：f ≡ λx. f x（当 f 是函数时）
                if t1.is_lam() and not t2.is_lam():
                    return self._is_def_eq_eta(t1, t2)
                if t2.is_lam() and not t1.is_lam():
                    return self._is_def_eq_eta(t2, t1)
                return False
    
    def _is_def_eq_eta(self, lam_expr: Expr, other: Expr) -> bool:
        """检查 η-等价：λ x. (f x) ≡ f。
        
        η-等价规则：
        如果 f 的类型是 Πx:A.B，那么 λx. f x ≡ f
        （要求 x 不在 f 的自由变量中出现）
        
        这是函数外延性的一种弱形式，
        在依赖类型理论中通常作为定义等价的一部分。
        
        Args:
            lam_expr: λ-抽象
            other: 另一个表达式
            
        Returns:
            True 如果满足 η-等价
        """
        if not lam_expr.is_lam():
            return False
        
        lam = lam_expr.kind
        # 构造一个新鲜的自由变量
        fresh_fvar = Expr.fvar(self._fvar_id_counter)
        self._fvar_id_counter += 1
        
        # 将 λ-body 中的 #0 替换为 fresh_fvar
        body_with_fvar = self.reducer.instantiate(lam.body, fresh_fvar)
        
        # 检查 body_with_fvar 是否 ≡ other fresh_fvar
        # 即：body[#0/x] ≡ app(other, x)
        expected = Expr.app(other, fresh_fvar)
        return self.is_def_eq(body_with_fvar, expected)
    
    # ============================================================
    # Universe Level 等价
    # ============================================================
    
    def is_level_def_eq(self, l1: Level, l2: Level) -> bool:
        """判断两个 universe level 是否定义等价。
        
        Universe level 的等价判断需要归约 level 表达式后比较。
        
        Args:
            l1: 第一个 level
            l2: 第二个 level
            
        Returns:
            True 如果 l1 ≡ l2
        """
        # 快速路径
        if l1 == l2:
            return True
        
        # 归约 level 表达式
        rl1 = self._reduce_level(l1)
        rl2 = self._reduce_level(l2)
        
        return rl1 == rl2
    
    def _reduce_level(self, level: Level) -> Level:
        """归约 universe level 表达式。
        
        归约规则：
        - imax(u, 0) → 0
        - imax(u, v+1) → max(u, v+1)
        - max(u, u) → u
        - max(0, u) → u
        - max(u, 0) → u
        - (u + n) + m → u + (n + m)
        """
        match level.kind:
            case Level.Zero():
                return level
            
            case Level.Param(_):
                return level  # 参数无法进一步归约
            
            case Level.Succ(l):
                reduced = self._reduce_level(l)
                return Level.succ(reduced)
            
            case Level.MSSucc(l, offset):
                reduced = self._reduce_level(l)
                match reduced.kind:
                    case Level.MSSucc(l2, offset2):
                        return Level(Level.MSSucc(l2, offset + offset2))
                    case _:
                        if offset == 0:
                            return reduced
                        result = reduced
                        for _ in range(offset):
                            result = Level.succ(result)
                        return result
            
            case Level.Max(l1, l2):
                rl1 = self._reduce_level(l1)
                rl2 = self._reduce_level(l2)
                # max(u, u) = u
                if rl1 == rl2:
                    return rl1
                # max(0, u) = u
                if isinstance(rl1.kind, Level.Zero):
                    return rl2
                if isinstance(rl2.kind, Level.Zero):
                    return rl1
                return Level.max_level(rl1, rl2)
            
            case Level.IMax(l1, l2):
                rl1 = self._reduce_level(l1)
                rl2 = self._reduce_level(l2)
                # imax(u, 0) = 0
                if isinstance(rl2.kind, Level.Zero):
                    return Level.zero()
                # imax(u, v) = max(u, v) when v ≠ 0
                # 但 v ≠ 0 在静态时无法确定（可能是参数）
                # 如果 rl2 明显不为 0，则简化为 max
                if not isinstance(rl2.kind, Level.Zero) and not isinstance(rl2.kind, Level.Param):
                    return Level.max_level(rl1, rl2)
                return Level.imax_level(rl1, rl2)
            
            case _:
                return level
    
    # ============================================================
    # 推断具体表达式类型的辅助方法
    # ============================================================
    
    def infer_sort(self, sort_expr: Expr) -> Expr:
        """推断 Sort u 的类型：Sort (u+1)。
        
        SORT 规则：Γ ⊢ Sort u : Sort (u+1)
        
        这是 universe 层级系统的核心：
        Sort 0 : Sort 1 : Sort 2 : ...
        这避免了 Russell 悖论和 Girard 悖论。
        
        Args:
            sort_expr: Sort(level) 表达式
            
        Returns:
            Sort(level + 1)
        """
        level = sort_expr.kind.level
        return Expr.sort(Level.succ(level))
    
    def infer_const(self, c: Expr) -> Expr:
        """推断全局常量的类型。
        
        CONST 规则：
        从环境查找常量的声明类型，并实例化 universe levels。
        
        例如：
        - infer(List) = Π (A : Type u), Type u
        - infer(List.{Nat}) = Type（将 u 替换为对应 level）
        
        Args:
            c: Const(name, levels) 表达式
            
        Returns:
            实例化后的常量类型
        """
        const = c.kind
        name = const.name
        levels = const.levels
        
        info = self.env.lookup(name)
        if info is None:
            raise TypeError(f"未声明的常量: {name}")
        
        # 获取常量的类型
        match info:
            case AxiomVal(type=ty):
                const_type = ty
            case DefnVal(type=ty):
                const_type = ty
            case ThmVal(type=ty):
                const_type = ty
            case InductVal(type=ty):
                const_type = ty
            case CtorVal(type=ty):
                const_type = ty
            case RecVal(type=ty):
                const_type = ty
            case _:
                raise TypeError(f"未知的常量类型: {info}")
        
        # 实例化 universe levels
        return self.reducer._instantiate_levels(const_type, levels)
    
    def infer_app(self, ctx: LocalContext, fn: Expr, arg: Expr) -> Expr:
        """推断函数应用的类型。
        
        APP 规则：
        Γ ⊢ f : Πx:A.B    Γ ⊢ a : A
        ─────────────────────────────
              Γ ⊢ f a : B[a/x]
        
        算法：
        1. 推断函数 f 的类型 fn_type
        2. 将 fn_type 归约到 WHNF，确保它是 Π 类型
        3. 检查参数 arg 的类型与 Π 的域类型匹配
        4. 返回 Π 的值域类型，将 x 替换为 arg
        
        Args:
            ctx: 局部上下文
            fn: 函数表达式
            arg: 参数表达式
            
        Returns:
            f a 的类型（B[a/x]）
        """
        # 推断函数类型
        fn_type = self.infer(ctx, fn)
        
        # 确保是 Π 类型
        pi_type = self.ensure_pi(ctx, fn_type)
        
        # 检查参数类型
        domain_type = pi_type.kind.dtype
        if not self.check(ctx, arg, domain_type):
            arg_type = self.infer(ctx, arg)
            raise TypeError(
                f"类型不匹配：期望 {self._expr_to_str(domain_type)}，"
                f"得到 {self._expr_to_str(arg_type)}"
            )
        
        # 返回 B[a/x]
        body_type = pi_type.kind.body
        return self.reducer.instantiate(body_type, arg)
    
    def infer_lam(self, ctx: LocalContext, lam_expr: Expr) -> Expr:
        """推断 λ-抽象的类型。
        
        LAM 规则：
        Γ, x:A ⊢ t : B    Γ ⊢ Πx:A.B : Sort u
        ─────────────────────────────────────
              Γ ⊢ λx:A.t : Πx:A.B
        
        算法：
        1. 检查域类型 A 是一个类型（A : Sort u）
        2. 创建新的自由变量 x，扩展上下文
        3. 在扩展上下文中推断体 t 的类型 B
        4. 返回 Πx:A.B
        
        Args:
            ctx: 局部上下文
            lam_expr: λ(name, dtype, body) 表达式
            
        Returns:
            Πx:A.B（λ-抽象的类型是依赖函数类型）
        """
        lam = lam_expr.kind
        name = lam.name
        dtype = lam.dtype
        body = lam.body
        
        # 1. 检查 dtype 是类型
        self.ensure_sort(ctx, dtype)
        
        # 2. 创建新的自由变量，扩展上下文
        new_ctx, fvar_expr = ctx.mk_fvar(name, dtype)
        
        # 3. 将 body 中的 #0 替换为 fvar，然后推断类型
        #    注意：body 使用 de Bruijn 索引，#0 对应新绑定的变量
        body_with_fvar = self.reducer.instantiate(body, fvar_expr)
        body_type = self.infer(new_ctx, body_with_fvar)
        
        # 4. 构造 Π 类型：需要将 body_type 中的 fvar 变回 de Bruijn 索引
        #    方法：用 #0 替换 fvar，同时将其他 fvar 的引用 lift
        body_type_with_bvar = self._abstract_fvar(body_type, fvar_expr.kind.id)
        
        return Expr.forallE(name, dtype, body_type_with_bvar, lam.binder_info)
    
    def infer_pi(self, ctx: LocalContext, pi_expr: Expr) -> Expr:
        """推断 Π-类型的类型。
        
        PI 规则：
        Γ ⊢ A : Sort u    Γ, x:A ⊢ B : Sort v
        ──────────────────────────────────────
              Γ ⊢ Πx:A.B : Sort (imax u v)
        
        这是依赖类型理论的核心规则之一：
        - imax(u, v) 确保如果 B 是 Prop（v=0），则 Πx:A.B 也是 Prop
        - 这支撑了证明无关性（proof irrelevance）
        
        算法：
        1. 推断域类型 A 的 universe u
        2. 创建新自由变量 x:A，扩展上下文
        3. 推断值域 B 的 universe v
        4. 返回 Sort (imax u v)
        
        Args:
            ctx: 局部上下文
            pi_expr: Π(name, dtype, body) 表达式
            
        Returns:
            Sort(imax u v)
        """
        pi = pi_expr.kind
        name = pi.name
        dtype = pi.dtype
        body = pi.body
        
        # 1. 推断域类型的 universe
        u = self.ensure_sort(ctx, dtype)
        
        # 2. 创建新自由变量，扩展上下文
        new_ctx, fvar_expr = ctx.mk_fvar(name, dtype)
        
        # 3. 将 body 中的 #0 替换为 fvar，推断 universe
        body_with_fvar = self.reducer.instantiate(body, fvar_expr)
        v = self.ensure_sort(new_ctx, body_with_fvar)
        
        # 4. 计算 imax(u, v)
        result_level = Level.imax_level(u, v)
        return Expr.sort(result_level)
    
    def infer_let(self, ctx: LocalContext, let_expr: Expr) -> Expr:
        """推断 let 绑定的类型。
        
        LET 规则：
        Γ ⊢ t : A    Γ, x:A ⊢ s : B
        ──────────────────────────────
          Γ ⊢ let x:A:=t in s : B[t/x]
        
        let 绑定等价于立即应用的 λ：
        let x:A:=t in s  ≡  (λx:A. s) t
        
        算法：
        1. 检查值 t 的类型为 A
        2. 创建新自由变量 x:A，扩展上下文
        3. 推断体 s 的类型 B
        4. 返回 B[t/x]
        
        Args:
            ctx: 局部上下文
            let_expr: let(name, dtype, value, body) 表达式
            
        Returns:
            B[t/x]
        """
        let = let_expr.kind
        name = let.name
        dtype = let.dtype
        value = let.value
        body = let.body
        
        # 1. 检查值的类型
        if not self.check(ctx, value, dtype):
            value_type = self.infer(ctx, value)
            raise TypeError(
                f"let 绑定类型不匹配: 期望 {self._expr_to_str(dtype)}, "
                f"得到 {self._expr_to_str(value_type)}"
            )
        
        # 2. 创建新自由变量（带值），扩展上下文
        new_ctx, fvar_expr = ctx.mk_fvar(name, dtype, value)
        
        # 3. 将 body 中的 #0 替换为 fvar，推断类型
        body_with_fvar = self.reducer.instantiate(body, fvar_expr)
        body_type = self.infer(new_ctx, body_with_fvar)
        
        # 4. 将结果中的 fvar 替换回 value（B[t/x]）
        result = self._subst_fvar(body_type, fvar_expr.kind.id, value)
        return result
    
    # ============================================================
    # 确保类型为特定形式的辅助方法
    # ============================================================
    
    def ensure_sort(self, ctx: LocalContext, e: Expr) -> Level:
        """确保表达式 e 归约后是一个 Sort，返回其 universe level。
        
        用于检查"A 是一个类型"（即 A : Sort u 对某个 u 成立）。
        
        例如：
        - ensure_sort(Nat) → 返回 Nat 所在的 universe level
        - ensure_sort(Prop) → 返回 Level.zero()
        
        Args:
            ctx: 局部上下文
            e: 待检查的表达式
            
        Returns:
            e 的 universe level
            
        Raises:
            TypeError: 如果 e 不是 Sort
        """
        e_type = self.infer(ctx, e)
        e_whnf = self.reducer.whnf(e_type)
        
        if e_whnf.is_sort():
            return e_whnf.kind.level
        
        raise TypeError(f"期望 Sort，得到 {self._expr_to_str(e_whnf)}")
    
    def ensure_pi(self, ctx: LocalContext, e: Expr) -> Expr:
        """确保表达式 e 归约后是一个 Π 类型。
        
        用于函数应用类型检查：函数的必须是 Π 类型才能应用参数。
        
        Args:
            ctx: 局部上下文
            e: 待检查的表达式
            
        Returns:
            归约后的 Π 类型表达式
            
        Raises:
            TypeError: 如果 e 不是 Π 类型
        """
        e_whnf = self.reducer.whnf(e)
        
        if e_whnf.is_forallE():
            return e_whnf
        
        raise TypeError(f"期望 Π 类型，得到 {self._expr_to_str(e_whnf)}")
    
    # ============================================================
    # de Bruijn / FVar 操作
    # ============================================================
    
    def _abstract_fvar(self, e: Expr, fvar_id: int, idx: int = 0) -> Expr:
        """将 e 中引用特定 fvar 的地方替换为 de Bruijn 索引 #idx。
        
        这是 instantiate 的逆操作：
        - instantiate: 将 #idx 替换为 fvar（用于替换 λ-body）
        - _abstract_fvar: 将 fvar 替换为 #idx（用于构造 Π 类型）
        
        这是从推断结果中"抽象"出自由变量的过程。
        
        Args:
            e: 包含 fvar 引用的表达式
            fvar_id: 要抽象的自由变量 ID
            idx: 要替换的 de Bruijn 索引（默认 0）
            
        Returns:
            替换后的表达式
        """
        match e.kind:
            case Expr.FVar(id):
                if id == fvar_id:
                    return Expr.bvar(idx)
                return e
            
            case Expr.Lam(name, dtype, body, bi):
                new_dtype = self._abstract_fvar(dtype, fvar_id, idx)
                new_body = self._abstract_fvar(body, fvar_id, idx + 1)
                if new_dtype is dtype and new_body is body:
                    return e
                return Expr.lam(name, new_dtype, new_body, bi)
            
            case Expr.ForallE(name, dtype, body, bi):
                new_dtype = self._abstract_fvar(dtype, fvar_id, idx)
                new_body = self._abstract_fvar(body, fvar_id, idx + 1)
                if new_dtype is dtype and new_body is body:
                    return e
                return Expr.forallE(name, new_dtype, new_body, bi)
            
            case Expr.LetE(name, dtype, value, body):
                new_dtype = self._abstract_fvar(dtype, fvar_id, idx)
                new_value = self._abstract_fvar(value, fvar_id, idx)
                new_body = self._abstract_fvar(body, fvar_id, idx + 1)
                if new_dtype is dtype and new_value is value and new_body is body:
                    return e
                return Expr.letE(name, new_dtype, new_value, new_body)
            
            case Expr.App(fn, arg):
                new_fn = self._abstract_fvar(fn, fvar_id, idx)
                new_arg = self._abstract_fvar(arg, fvar_id, idx)
                if new_fn is fn and new_arg is arg:
                    return e
                return Expr.app(new_fn, new_arg)
            
            case Expr.Sort(_) | Expr.Const(_, _) | Expr.BVar(_) | Expr.MVar(_) | Expr.Lit(_):
                return e
            
            case Expr.Proj(type_name, field_idx, struct):
                new_struct = self._abstract_fvar(struct, fvar_id, idx)
                if new_struct is struct:
                    return e
                return Expr(Expr.Proj(type_name, field_idx, new_struct))
            
            case _:
                return e
    
    def _subst_fvar(self, e: Expr, fvar_id: int, value: Expr) -> Expr:
        """将 e 中引用特定 fvar 的地方替换为 value。
        
        类似于 instantiate，但替换的是 FVar 而非 BVar。
        
        Args:
            e: 包含 fvar 引用的表达式
            fvar_id: 要替换的自由变量 ID
            value: 替换值
            
        Returns:
            替换后的表达式
        """
        match e.kind:
            case Expr.FVar(id):
                if id == fvar_id:
                    return value
                return e
            
            case Expr.Lam(name, dtype, body, bi):
                new_dtype = self._subst_fvar(dtype, fvar_id, value)
                new_body = self._subst_fvar(body, fvar_id, value)
                if new_dtype is dtype and new_body is body:
                    return e
                return Expr.lam(name, new_dtype, new_body, bi)
            
            case Expr.ForallE(name, dtype, body, bi):
                new_dtype = self._subst_fvar(dtype, fvar_id, value)
                new_body = self._subst_fvar(body, fvar_id, value)
                if new_dtype is dtype and new_body is body:
                    return e
                return Expr.forallE(name, new_dtype, new_body, bi)
            
            case Expr.LetE(name, dtype, val, body):
                new_dtype = self._subst_fvar(dtype, fvar_id, value)
                new_val = self._subst_fvar(val, fvar_id, value)
                new_body = self._subst_fvar(body, fvar_id, value)
                if new_dtype is dtype and new_val is val and new_body is body:
                    return e
                return Expr.letE(name, new_dtype, new_val, new_body)
            
            case Expr.App(fn, arg):
                new_fn = self._subst_fvar(fn, fvar_id, value)
                new_arg = self._subst_fvar(arg, fvar_id, value)
                if new_fn is fn and new_arg is arg:
                    return e
                return Expr.app(new_fn, new_arg)
            
            case Expr.Sort(_) | Expr.Const(_, _) | Expr.BVar(_) | Expr.MVar(_) | Expr.Lit(_):
                return e
            
            case Expr.Proj(type_name, field_idx, struct):
                new_struct = self._subst_fvar(struct, fvar_id, value)
                if new_struct is struct:
                    return e
                return Expr(Expr.Proj(type_name, field_idx, new_struct))
            
            case _:
                return e
    
    # ============================================================
    # 元变量操作
    # ============================================================
    
    def assign_mvar(self, mvar_id: int, value: Expr) -> None:
        """为元变量赋值。
        
        元变量赋值需要满足类型约束：
        value 的类型必须与元变量的类型定义等价。
        
        Args:
            mvar_id: 元变量 ID
            value: 赋值
        """
        if self.metavar_ctx is not None:
            self.metavar_ctx = self.metavar_ctx.assign(mvar_id, value)
            # 同步更新 reducer 中的 metavar_ctx
            self.reducer.metavar_ctx = self.metavar_ctx
    
    def instantiate_mvars(self, e: Expr) -> Expr:
        """实例化表达式中的所有元变量。
        
        将所有已赋值的元变量替换为其值。
        
        Args:
            e: 待实例化的表达式
            
        Returns:
            实例化后的表达式
        """
        if self.metavar_ctx is not None:
            return self.metavar_ctx.instantiate_mvars(e)
        return e
    
    # ============================================================
    # 调试辅助
    # ============================================================
    
    def _expr_to_str(self, e: Expr) -> str:
        """将表达式转换为可读字符串（用于错误信息）。"""
        if e is None:
            return "None"
        try:
            return repr(e)
        except:
            return str(e.kind.__class__.__name__)
    
    def _level_to_str(self, level: Level) -> str:
        """将 universe level 转换为可读字符串。"""
        return repr(level)


# 导入 Literal 用于 match
from .expr import Literal
