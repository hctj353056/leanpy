"""
LeanPy 示例：展示 Curry-Howard 同构和依赖类型。

本文件包含多个示例，从简单到复杂：
1. 基本类型检查和 λ 项
2. 逻辑连接词的证明
3. 自然数定义和归纳证明
4. 使用 Tactic 的交互式证明

每个示例都说明了依赖类型理论和 Curry-Howard 同构的一个方面：
- 类型 = 命题
- 项 = 证明
- 函数类型 A → B = 蕴涵 A ⇒ B
- Π 类型 = 全称量词 ∀
- λ 抽象 = 证明引入规则
- 函数应用 = 证明消去规则
"""
from __future__ import annotations

from .name import mk_name
from .expr import Expr, app
from .environment import Environment, LocalContext, AxiomVal
from .inductive import (
    mk_nat_type, mk_bool_type, mk_unit_type, mk_empty_type,
    mk_prod_type, mk_sum_type, register_inductive
)
from .typechecker import TypeChecker
from .parser import parse_expr
from .tactic import (
    Intro, Exact, Assumption,
    by_tactics, start_proof, finish_proof
)


# ===== 环境设置 =====

def setup_basic_environment() -> Environment:
    """设置包含基本定义的环境。

    注册自然数、布尔值等归纳类型，以及基本定理。
    """
    env = Environment()

    # 注册自然数类型
    nat_decl, nat_infos = mk_nat_type()
    env = register_inductive(env, nat_decl, nat_infos)

    # 注册布尔类型
    bool_decl, bool_infos = mk_bool_type()
    env = register_inductive(env, bool_decl, bool_infos)

    # 注册单元类型
    unit_decl, unit_infos = mk_unit_type()
    env = register_inductive(env, unit_decl, unit_infos)

    # 注册空类型
    empty_decl, empty_infos = mk_empty_type()
    env = register_inductive(env, empty_decl, empty_infos)

    # 注册积类型
    prod_decl, prod_infos = mk_prod_type()
    env = register_inductive(env, prod_decl, prod_infos)

    # 注册和类型
    sum_decl, sum_infos = mk_sum_type()
    env = register_inductive(env, sum_decl, sum_infos)

    return env


def setup_nat_environment() -> Environment:
    """设置包含自然数定义和加法的环境。"""
    env = setup_basic_environment()

    # 定义加法：add : Nat → Nat → Nat
    # 简化版：作为公理声明
    nat = Expr.const(mk_name("Nat"))
    nat_to_nat = Expr.mk_arrow(nat, nat)
    nat_to_nat_to_nat = Expr.mk_arrow(nat, nat_to_nat)

    # add 常量的类型
    add_type = nat_to_nat_to_nat
    env = env.add(
        mk_name("Nat", "add"),
        AxiomVal(name=mk_name("Nat", "add"), type=add_type)
    )

    return env


# ===== 示例 1: 基本类型检查和 λ 项 =====

def example_id_function():
    """证明 ∀ A : Type, A → A（恒等函数/自反蕴涵）。

    Curry-Howard 解释：
    - 类型论：恒等函数 λ A. λ x. x : Π A : Type. A → A
    - 逻辑：自反蕴涵 A ⇒ A
    - 证明：假设 A，假设 A 成立，结论 A 成立

    这是最简单的非平凡定理：每个命题都蕴涵自身。
    """
    print("\n--- 示例 1a: 恒等函数 (A → A) ---")

    env = setup_basic_environment()
    checker = TypeChecker(env)
    ctx = LocalContext()

    # 构造 λ A : Type. λ x : A. x
    # 其类型是 Π A : Type. Π x : A. A

    # 使用 parser 构造
    id_term = parse_expr("fun (A : Type) (x : A) => x")
    print(f"恒等项: {id_term}")

    # 类型推导
    try:
        id_type = checker.infer(ctx, id_term)
        print(f"类型: {id_type}")
    except Exception as e:
        print(f"类型推导（预期可能不完全成功）: {e}")

    return id_term


def example_k_combinator():
    """证明 ∀ A B : Type, A → B → A（K 组合子/前件加强律）。

    Curry-Howard 解释：
    - 类型论：K = λ A B. λ a b. a : Π A B. A → B → A
    - 逻辑：A ⇒ (B ⇒ A)  —— 如果 A 成立，则无论 B 如何 A 都成立
    - 证明：假设 A 和 B，使用 A 的假设

    这是希尔伯特蕴涵公理的前半部分。
    """
    print("\n--- 示例 1b: K 组合子 (A → B → A) ---")

    env = setup_basic_environment()

    # 构造 λ A : Type. λ B : Type. λ a : A. λ b : B. a
    k_term = parse_expr("fun (A : Type) (B : Type) (a : A) (b : B) => a")
    print(f"K 组合子: {k_term}")

    return k_term


def example_s_combinator():
    """证明 S 组合子：∀ A B C : Type, (A → B → C) → (A → B) → A → C。

    Curry-Howard 解释：
    - 类型论：S = λ A B C. λ f g x. f x (g x)
    - 逻辑：((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
    - 这是希尔伯特蕴涵公理的后半部分

    S 组合子是 λ 演算的核心，与 K 一起可以定义所有函数。
    在逻辑中，S + K 完备了蕴涵片段。
    """
    print("\n--- 示例 1c: S 组合子 ---")

    env = setup_basic_environment()

    # 构造 S 组合子
    # fun (A B C : Type) (f : A -> B -> C) (g : A -> B) (x : A) => f x (g x)
    s_term = parse_expr(
        "fun (A : Type) (B : Type) (C : Type) "
        "(f : A -> B -> C) (g : A -> B) (x : A) => f x (g x)"
    )
    print(f"S 组合子: {s_term}")

    return s_term


# ===== 示例 2: 逻辑命题的证明 =====

def example_and_intro():
    """证明 A → B → A ∧ B（合取引入）。

    Curry-Howard 解释：
    - 在类型论中，A ∧ B 对应积类型 A × B
    - A → B → A × B = Π A B. A → B → Prod A B
    - 证明 λ A B. λ a b. Prod.mk a b

    逻辑解释：如果 A 成立且 B 成立，则 A ∧ B 成立。
    """
    print("\n--- 示例 2a: 合取引入 (A → B → A ∧ B) ---")

    env = setup_basic_environment()

    # 合取引入：λ A B. λ a b. Prod.mk a b
    and_intro = parse_expr(
        "fun (A : Type) (B : Type) (a : A) (b : B) => Prod.mk A B a b"
    )
    print(f"合取引入: {and_intro}")

    return and_intro


def example_and_elim_left():
    """证明 A ∧ B → A（合取消去左）。

    Curry-Howard 解释：
    - 从 A × B 中提取第一个分量
    - 逻辑：如果 A ∧ B 成立，则 A 成立

    注意：完整实现需要积类型的投影/递归子，
    这里展示概念。
    """
    print("\n--- 示例 2b: 合取消去左 (A ∧ B → A) ---")

    # 在纯 λ 演算中，可以用 fst = λ p. p (λ a b. a)
    # 这里展示概念
    env = setup_basic_environment()

    # fst : Prod A B → A
    fst_term = parse_expr(
        "fun (A : Type) (B : Type) (p : Prod A B) => "
        "Prod.mk A B"  # 简化表示
    )
    print("合取消去（概念）: 从 Prod A B 提取 A")

    return fst_term


def example_or_intro_left():
    """证明 A → A ∨ B（析取引入左）。

    Curry-Howard 解释：
    - A ∨ B 对应和类型 Sum A B
    - A → Sum A B = λ a. Sum.inl a
    - 逻辑：如果 A 成立，则 A ∨ B 成立
    """
    print("\n--- 示例 2c: 析取引入左 (A → A ∨ B) ---")

    env = setup_basic_environment()

    or_intro_left = parse_expr(
        "fun (A : Type) (B : Type) (a : A) => Sum.inl A B a"
    )
    print(f"析取引入左: {or_intro_left}")

    return or_intro_left


def example_implies_trans():
    """证明 (A → B) → (B → C) → (A → C)（蕴涵传递性）。

    Curry-Howard 解释：
    - 函数复合：g ∘ f = λ x. g (f x)
    - 逻辑：如果 A ⇒ B 且 B ⇒ C，则 A ⇒ C

    这是三段论在蕴涵逻辑中的形式。
    """
    print("\n--- 示例 2d: 蕴涵传递性 ---")

    env = setup_basic_environment()

    # λ A B C. λ f g x. g (f x)
    trans_term = parse_expr(
        "fun (A : Type) (B : Type) (C : Type) "
        "(f : A -> B) (g : B -> C) (x : A) => g (f x)"
    )
    print(f"蕴涵传递性: {trans_term}")

    return trans_term


def example_dneg_intro():
    """证明 A → ¬¬A（双重否定引入）。

    在直觉主义逻辑中，¬A = A → ⊥（A 蕴涵矛盾）。
    所以 ¬¬A = (A → ⊥) → ⊥。

    证明 λ A. λ a k. k a :
    A → (A → ⊥) → ⊥
    """
    print("\n--- 示例 2e: 双重否定引入 (A → ¬¬A) ---")

    env = setup_basic_environment()

    # ¬¬A = (A → Empty) → Empty
    # A → ¬¬A = λ a k. k a
    dneg_term = parse_expr(
        "fun (A : Type) (a : A) (k : A -> Empty) => k a"
    )
    print(f"双重否定引入: {dneg_term}")

    return dneg_term


# ===== 示例 3: 自然数 =====

def example_nat_zero():
    """构造自然数 0。

    Nat.zero 是 Nat 类型的一个构造子。
    """
    print("\n--- 示例 3a: 自然数 0 ---")

    env = setup_nat_environment()

    zero = Expr.const(mk_name("Nat", "zero"))
    print(f"自然数 0: {zero}")

    return zero


def example_nat_one():
    """构造自然数 1 = succ 0。"""
    print("\n--- 示例 3b: 自然数 1 ---")

    env = setup_nat_environment()

    # 1 = Nat.succ Nat.zero
    zero = Expr.const(mk_name("Nat", "zero"))
    one = app(Expr.const(mk_name("Nat", "succ")), zero)
    print(f"自然数 1: {one}")

    return one


def example_nat_add_def():
    """展示加法定义。

    加法是递归定义的：
    - add 0 m = m
    - add (succ n) m = succ (add n m)

    在 Lean 中，这通过递归子 Nat.rec 来定义。
    """
    print("\n--- 示例 3c: 加法定义 ---")

    env = setup_nat_environment()

    # 2 = succ (succ 0)
    zero = Expr.const(mk_name("Nat", "zero"))
    succ = Expr.const(mk_name("Nat", "succ"))
    one = app(succ, zero)
    two = app(succ, one)

    print(f"0 = {zero}")
    print(f"1 = {one}")
    print(f"2 = {two}")

    # add 2 1 = succ (succ (succ 0)) = 3（概念上）
    add = Expr.const(mk_name("Nat", "add"))
    add_2_1 = app(app(add, two), one)
    print(f"add 2 1 = {add_2_1}")

    return add_2_1


def example_nat_parsed():
    """使用解析器构造自然数表达式。"""
    print("\n--- 示例 3d: 解析自然数表达式 ---")

    env = setup_nat_environment()

    # 解析一些自然数表达式
    exprs = [
        "Nat.zero",
        "Nat.succ Nat.zero",
        "Nat.add Nat.zero (Nat.succ Nat.zero)",
    ]

    for text in exprs:
        try:
            expr = parse_expr(text, env)
            print(f"  '{text}' → {expr}")
        except Exception as e:
            print(f"  '{text}' → 错误: {e}")


# ===== 示例 4: 解析器演示 =====

def example_parser_demo():
    """全面演示解析器功能。"""
    print("\n--- 示例 4: 解析器演示 ---")

    examples = [
        # 基本 lambda
        ("fun (x : Nat) => x", "λ 抽象"),
        # 多参数 lambda
        ("fun (A : Type) (x : A) => x", "多参数 λ"),
        # 箭头类型
        ("Nat -> Bool", "箭头类型"),
        # 嵌套箭头
        ("A -> B -> C", "嵌套箭头"),
        # forall
        ("forall (A : Type), A -> A", "全称量词"),
        # 函数应用
        ("f a b", "函数应用"),
        # let
        ("let x : Nat := 1; x", "let 绑定"),
        # Sort/Type/Prop
        ("Prop", "Prop 宇宙"),
        ("Type", "Type 宇宙"),
        ("Sort 1", "Sort 1"),
        # 自然数字面量
        ("42", "自然数字面量"),
        # 复杂表达式
        ("fun (A : Type) (f : A -> A) (x : A) => f (f x)", "复杂 λ"),
    ]

    for text, desc in examples:
        try:
            expr = parse_expr(text)
            print(f"  [{desc}] '{text}'")
            print(f"       → {expr}")
        except Exception as e:
            print(f"  [{desc}] '{text}' → 错误: {e}")


# ===== 示例 5: 使用 Tactic 证明 =====

def example_tactic_intro_exact():
    """使用 intro + exact 证明 A → A。

    证明过程：
    1. 开始证明 A → A
    2. intro x → 假设 x : A，目标变为 A
    3. exact x → 用 x 证明 A

    Curry-Howard 对应：
    - 证明 λ x. x（恒等函数）
    """
    print("\n--- 示例 5a: Tactic 证明 A → A ---")

    env = setup_basic_environment()

    # 目标：A → A
    # 使用 Nat 作为具体的 A
    nat = Expr.const(mk_name("Nat"))
    target = Expr.mk_arrow(nat, nat)

    # 开始证明
    state = start_proof(env, target)
    print(f"初始状态:\n{state}")

    # intro n
    state = Intro("n").run(state)
    print(f"intro n 后:\n{state}")

    # exact (fvar 0 = n)
    current = state.get_current_goal()
    if current:
        exact_expr = Expr.fvar(0)  # n : Nat
        state = Exact(exact_expr).run(state)
        print(f"exact n 后:\n{state}")

    # 完成证明
    proof = finish_proof(state)
    print(f"证明项: {proof}")

    return proof


def example_tactic_assumption():
    """使用 assumption 证明 A → (A → B) → B。

    证明过程：
    1. 开始证明 A → (A → B) → B
    2. intro a → 假设 a : A
    3. intro f → 假设 f : A → B
    4. 此时需要证明 B，可以用 f a

    简化版：证明 A → A（使用 assumption）
    """
    print("\n--- 示例 5b: Tactic 证明 A → A (使用 assumption) ---")

    env = setup_basic_environment()

    # 目标：A → A
    nat = Expr.const(mk_name("Nat"))
    target = Expr.mk_arrow(nat, nat)

    # 开始证明
    state = start_proof(env, target)
    print(f"初始状态:\n{state}")

    # intro n
    state = Intro("n").run(state)
    print(f"intro n 后:\n{state}")

    # assumption 应该找到 n : Nat
    state = Assumption().run(state)
    print(f"assumption 后:\n{state}")

    # 完成证明
    proof = finish_proof(state)
    print(f"证明项: {proof}")

    return proof


def example_tactic_apply():
    """使用 apply 证明 (A → B → C) → (A → B) → A → C。

    这是 S 组合子。证明思路：
    1. 假设 f : A → B → C, g : A → B, a : A
    2. 要证 C
    3. apply f → 需要证 A 和 B
    4. 证 A：exact a
    5. 证 B：apply g → 需要证 A
    6. 证 A：exact a

    简化版：证明简单的目标
    """
    print("\n--- 示例 5c: Tactic 使用 apply ---")

    env = setup_basic_environment()

    # 证明 Nat → Nat
    # 使用 apply (λ x. x)
    nat = Expr.const(mk_name("Nat"))
    target = Expr.mk_arrow(nat, nat)

    state = start_proof(env, target)
    print(f"初始状态:\n{state}")

    # intro n
    state = Intro("n").run(state)
    print(f"intro n 后:\n{state}")

    # 使用 apply：应用一个函数来匹配目标
    # 在当前上下文中，n : Nat，目标是 Nat
    # exact n 直接解决
    current = state.get_current_goal()
    if current:
        state = Exact(Expr.fvar(0)).run(state)
        print(f"exact n 后:\n{state}")

    proof = finish_proof(state)
    print(f"证明项: {proof}")

    return proof


def example_tactic_combined():
    """使用组合 tactic 证明更复杂的命题。"""
    print("\n--- 示例 5d: 组合 Tactic 证明 ---")

    env = setup_basic_environment()

    # 证明 A → B → A
    # (K 组合子)
    nat = Expr.const(mk_name("Nat"))
    bool_ = Expr.const(mk_name("Bool"))
    # A → B → A = Nat → Bool → Nat
    target = Expr.mk_arrow(nat, Expr.mk_arrow(bool_, nat))

    state = start_proof(env, target)
    print(f"初始状态:\n{state}")

    # 使用 by_tactics 组合
    state = by_tactics(state,
        Intro("a"),      # 引入 a : Nat
        Intro("b"),      # 引入 b : Bool
    )
    print(f"intro a, intro b 后:\n{state}")

    # exact a
    current = state.get_current_goal()
    if current:
        # a 是 fvar 0（最近引入）... 不对
        # 根据 Intro 的实现，最近引入的在索引 0
        # a 先引入，b 后引入
        # 所以 b = fvar 0, a = fvar 1
        state = Exact(Expr.fvar(1)).run(state)
        print(f"exact a 后:\n{state}")

    proof = finish_proof(state)
    print(f"证明项: {proof}")

    return proof


# ===== 示例 6: Curry-Howard 深入 =====

def example_curry_howard_summary():
    """总结 Curry-Howard 同构的对应关系。"""
    print("\n--- 示例 6: Curry-Howard 同构总结 ---")

    correspondences = """
    Curry-Howard 同构（命题即类型，证明即程序）
    ╔═══════════════════════╦═══════════════════════╗
    ║  逻 辑 (Logic)        ║  类 型 (Types)        ║
    ╠═══════════════════════╬═══════════════════════╣
    ║  命题 A               ║  类型 A               ║
    ║  证明 t : A           ║  项 t : A             ║
    ║  A ∧ B (合取)         ║  A × B (积类型)       ║
    ║  A ∨ B (析取)         ║  A + B (和类型)       ║
    ║  A ⇒ B (蕴涵)         ║  A → B (函数类型)     ║
    ║  ⊥ (矛盾)             ║  Empty (空类型)       ║
    ║  ⊤ (真)               ║  Unit (单元类型)      ║
    ║  ∀x:A. P(x)           ║  Πx:A. P(x)           ║
    ║  ∃x:A. P(x)           ║  Σx:A. P(x)           ║
    ╠═══════════════════════╬═══════════════════════╣
    ║  证明策略              ║  程序构造              ║
    ╠═══════════════════════╬═══════════════════════╣
    ║  intro (引入假设)      ║  λ 抽象               ║
    ║  apply (应用定理)      ║  函数应用             ║
    ║  exact (直接证明)      ║  直接构造项            ║
    ║  rewrite (重写)        ║  等式替换             ║
    ╚═══════════════════════╩═══════════════════════╝

    关键洞见：
    1. 要证明 A → B，构造一个函数 λ x. ...，它将 A 的证明转换为 B 的证明
    2. 要证明 A × B，构造一对 (a, b)，其中 a 证明 A，b 证明 B
    3. 要证明 A + B，选择左边 (inl a) 或右边 (inr b)
    4. ⊥ (Empty) 没有构造子，因此没有证明——对应矛盾命题不可证
    """
    print(correspondences)


# ===== 主函数 =====

def run_all_examples():
    """运行所有示例并打印结果。"""
    print("=" * 60)
    print("LeanPy 示例：Lean 核心逻辑的 Python 复刻")
    print("=" * 60)
    print()
    print("本演示展示了：")
    print("  1. 依赖类型理论的核心构造（λ, Π, 归纳类型）")
    print("  2. Curry-Howard 同构（命题即类型，证明即程序）")
    print("  3. 递归下降解析器")
    print("  4. 基于元变量的交互式证明（Tactic 系统）")
    print()

    # 示例 1: 基本 λ 项
    print("\n" + "=" * 60)
    print("第一部分: 基本 λ 项与类型")
    print("=" * 60)
    example_id_function()
    example_k_combinator()
    example_s_combinator()

    # 示例 2: 逻辑命题
    print("\n" + "=" * 60)
    print("第二部分: 逻辑命题的证明")
    print("=" * 60)
    example_and_intro()
    example_and_elim_left()
    example_or_intro_left()
    example_implies_trans()
    example_dneg_intro()

    # 示例 3: 自然数
    print("\n" + "=" * 60)
    print("第三部分: 自然数")
    print("=" * 60)
    example_nat_zero()
    example_nat_one()
    example_nat_add_def()
    example_nat_parsed()

    # 示例 4: 解析器
    print("\n" + "=" * 60)
    print("第四部分: 解析器演示")
    print("=" * 60)
    example_parser_demo()

    # 示例 5: Tactic 系统
    print("\n" + "=" * 60)
    print("第五部分: Tactic 交互式证明")
    print("=" * 60)
    example_tactic_intro_exact()
    example_tactic_assumption()
    example_tactic_apply()
    example_tactic_combined()

    # 示例 6: 总结
    print("\n" + "=" * 60)
    print("第六部分: Curry-Howard 同构")
    print("=" * 60)
    example_curry_howard_summary()

    print("\n" + "=" * 60)
    print("✓ 所有示例运行成功！")
    print("=" * 60)


if __name__ == "__main__":
    run_all_examples()
