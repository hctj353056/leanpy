"""
LeanPy 核心测试：归约器和类型检查器。

这些测试覆盖了 β/δ/ι/ζ 归约、WHNF 算法、类型推断、
类型检查和定义等价判断。
"""
from __future__ import annotations
import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from leanpy.name import Name, mk_name
from leanpy.level import Level
from leanpy.expr import Expr, BinderInfo
from leanpy.environment import (
    Environment, LocalContext, MetavarContext,
    AxiomVal, DefnVal, ThmVal
)
from leanpy.reducer import Reducer
from leanpy.typechecker import TypeChecker


def test_beta_reduction():
    """β-归约测试：(λ x : A. t) a → t[a/x]"""
    print("\n=== Beta Reduction ===")
    env = Environment()
    reducer = Reducer(env)
    
    # (λ x : Type. x) Type → Type
    id_fn = Expr.lam("x", Expr.Type, Expr.bvar(0))
    app1 = Expr.app(id_fn, Expr.Type)
    assert reducer.beta_reduce(app1) == Expr.Type
    assert reducer.whnf(app1) == Expr.Type
    print("✓ (λx.x) Type → Type")
    
    # (λ x : Type. C) Type → C
    const_ref = Expr.const(mk_name("C"))
    const_fn = Expr.lam("x", Expr.Type, const_ref)
    app2 = Expr.app(const_fn, Expr.Type)
    assert reducer.beta_reduce(app2) == const_ref
    print("✓ (λx.C) Type → C")
    
    # Nested: (λ f. f Type) (λ x. x) → Type
    app3 = Expr.app(
        Expr.lam("f", Expr.forallE("_", Expr.Type, Expr.Type),
                 Expr.app(Expr.bvar(0), Expr.Type)),
        id_fn
    )
    assert reducer.whnf(app3) == Expr.Type
    print("✓ (λf.f Type)(λx.x) → Type")
    
    # Non-redex: C a (where C is not λ)
    non_redex = Expr.app(Expr.const(mk_name("C")), Expr.Type)
    assert reducer.beta_reduce(non_redex) is None
    print("✓ C Type is not a β-redex")


def test_delta_reduction():
    """δ-归约测试：展开全局常量定义。"""
    print("\n=== Delta Reduction ===")
    env = Environment()
    
    # Define myDef := Prop
    myDef_name = mk_name("myDef")
    env = env.add(myDef_name, DefnVal(myDef_name, Expr.Type, Expr.Prop))
    
    reducer = Reducer(env)
    myDef_ref = Expr.const(myDef_name)
    
    assert reducer.delta_reduce(myDef_ref) == Expr.Prop
    assert reducer.whnf(myDef_ref) == Expr.Prop
    print("✓ myDef (:= Prop) → Prop")
    
    # Opaque definitions should not reduce
    opaque_name = mk_name("opaqueDef")
    env2 = env.add(opaque_name, DefnVal(opaque_name, Expr.Type, Expr.Prop, is_opaque=True))
    reducer2 = Reducer(env2)
    opaque_ref = Expr.const(opaque_name)
    assert reducer2.delta_reduce(opaque_ref) is None
    print("✓ Opaque definition does not reduce")
    
    # Axioms have no value to reduce
    ax_name = mk_name("myAx")
    env3 = env.add(ax_name, AxiomVal(ax_name, Expr.Prop))
    reducer3 = Reducer(env3)
    ax_ref = Expr.const(ax_name)
    assert reducer3.delta_reduce(ax_ref) is None
    print("✓ Axiom has no δ-reduction")


def test_zeta_reduction():
    """ζ-归约测试：let x := t in s → s[t/x]。"""
    print("\n=== Zeta Reduction ===")
    env = Environment()
    reducer = Reducer(env)
    
    # let x : Type := Prop in x → Prop
    let1 = Expr.letE("x", Expr.Type, Expr.Prop, Expr.bvar(0))
    assert reducer.zeta_reduce(let1) == Expr.Prop
    assert reducer.whnf(let1) == Expr.Prop
    print("✓ let x:Type:=Prop in x → Prop")
    
    # let x : Type := Prop in Type → Type
    let2 = Expr.letE("x", Expr.Type, Expr.Prop, Expr.Type)
    assert reducer.zeta_reduce(let2) == Expr.Type
    print("✓ let x:Type:=Prop in Type → Type")
    
    # Non-let expression
    assert reducer.zeta_reduce(Expr.Type) is None
    print("✓ Type is not a ζ-redex")


def test_whnf():
    """WHNF 算法测试。"""
    print("\n=== WHNF ===")
    env = Environment()
    reducer = Reducer(env)
    
    # λ is already WHNF
    lam = Expr.lam("x", Expr.Type, Expr.bvar(0))
    assert reducer.whnf(lam) == lam
    print("✓ WHNF(λx.x) = λx.x")
    
    # Π is already WHNF
    pi = Expr.forallE("x", Expr.Type, Expr.Type)
    assert reducer.whnf(pi) == pi
    print("✓ WHNF(Πx:Type.Type) = Πx:Type.Type")
    
    # Sort is WHNF
    assert reducer.whnf(Expr.Type) == Expr.Type
    print("✓ WHNF(Type) = Type")
    
    # FVar is WHNF
    fvar = Expr.fvar(0)
    assert reducer.whnf(fvar) == fvar
    print("✓ WHNF(fv0) = fv0")
    
    # BVar is WHNF
    bvar = Expr.bvar(0)
    assert reducer.whnf(bvar) == bvar
    print("✓ WHNF(#0) = #0")


def test_definitional_equality():
    """定义等价测试。"""
    print("\n=== Definitional Equality ===")
    env = Environment()
    myDef_name = mk_name("myDef")
    env = env.add(myDef_name, DefnVal(myDef_name, Expr.Type, Expr.Prop))
    tc = TypeChecker(env)
    
    # Reflexivity
    assert tc.is_def_eq(Expr.Type, Expr.Type)
    assert tc.is_def_eq(Expr.Prop, Expr.Prop)
    print("✓ Type ≡ Type, Prop ≡ Prop")
    
    # Symmetry
    assert tc.is_def_eq(Expr.Type, Expr.Type)
    print("✓ Symmetry")
    
    # Inequality
    assert not tc.is_def_eq(Expr.Type, Expr.Prop)
    print("✓ Type ≢ Prop")
    
    # Beta equivalence
    id_fn = Expr.lam("x", Expr.Type, Expr.bvar(0))
    app = Expr.app(id_fn, Expr.Type)
    assert tc.is_def_eq(app, Expr.Type)
    print("✓ (λx.x) Type ≡ Type")
    
    # Delta equivalence
    assert tc.is_def_eq(Expr.const(myDef_name), Expr.Prop)
    print("✓ myDef ≡ Prop (delta)")
    
    # Zeta equivalence
    let1 = Expr.letE("x", Expr.Type, Expr.Prop, Expr.bvar(0))
    assert tc.is_def_eq(let1, Expr.Prop)
    print("✓ let x:Type:=Prop in x ≡ Prop")
    
    # Combined: beta + delta
    def_fn = Expr.lam("x", Expr.Type, Expr.const(myDef_name))
    app2 = Expr.app(def_fn, Expr.Type)
    assert tc.is_def_eq(app2, Expr.Prop)
    print("✓ (λx.myDef) Type ≡ Prop (beta+delta)")


def test_type_inference():
    """类型推断测试。"""
    print("\n=== Type Inference ===")
    
    # Setup: A : Prop (axiom)
    env = Environment()
    A_name = mk_name("A")
    env = env.add(A_name, AxiomVal(A_name, Expr.Prop))
    tc = TypeChecker(env)
    ctx = LocalContext()
    A_ref = Expr.const(A_name)
    
    # Sort inference
    t = tc.infer(ctx, Expr.Type)
    assert t.is_sort()
    print(f"✓ infer(Type) = {t}")
    
    # Prop inference
    t = tc.infer(ctx, Expr.Prop)
    assert t.is_sort()
    print(f"✓ infer(Prop) = {t}")
    
    # Constant inference
    t = tc.infer(ctx, A_ref)
    assert t == Expr.Prop
    print(f"✓ infer(A) = {t}")
    
    # Lambda inference: (λ x : Prop. x) : (Π x : Prop. Prop)
    lam = Expr.lam("x", Expr.Prop, Expr.bvar(0))
    t = tc.infer(ctx, lam)
    assert t.is_forallE()
    assert t.kind.dtype == Expr.Prop
    print(f"✓ infer(λx:Prop.x) = {t}")
    
    # Pi inference
    pi = Expr.forallE("x", Expr.Prop, Expr.Prop)
    t = tc.infer(ctx, pi)
    assert t.is_sort()
    print(f"✓ infer(Πx:Prop.Prop) = {t}")
    
    # Application inference
    app = Expr.app(lam, A_ref)
    t = tc.infer(ctx, app)
    assert t == Expr.Prop
    print(f"✓ infer((λx:Prop.x) A) = {t}")
    
    # Let inference
    let_expr = Expr.letE("x", Expr.Type, Expr.Prop, Expr.bvar(0))
    t = tc.infer(ctx, let_expr)
    assert t == Expr.Type  # Declared type, not value type
    print(f"✓ infer(let x:Type:=Prop in x) = {t}")


def test_type_checking():
    """类型检查测试。"""
    print("\n=== Type Checking ===")
    env = Environment()
    A_name = mk_name("A")
    env = env.add(A_name, AxiomVal(A_name, Expr.Prop))
    tc = TypeChecker(env)
    ctx = LocalContext()
    A_ref = Expr.const(A_name)
    
    # A : Prop
    assert tc.check(ctx, A_ref, Expr.Prop)
    print("✓ check(A, Prop) = True")
    
    # A : Type should be False (A : Prop, Prop ≢ Type)
    assert not tc.check(ctx, A_ref, Expr.Type)
    print("✓ check(A, Type) = False (A : Prop, Prop ≢ Type)")
    
    # Prop : Type
    assert tc.check(ctx, Expr.Prop, Expr.Type)
    print("✓ check(Prop, Type) = True")
    
    # Type : Type 1
    assert tc.check(ctx, Expr.Type, Expr.sort(Level.succ(Level.TYPE_0)))
    print("✓ check(Type, Type 1) = True")
    
    # (λx:Prop.x) A : Prop
    lam = Expr.lam("x", Expr.Prop, Expr.bvar(0))
    app = Expr.app(lam, A_ref)
    assert tc.check(ctx, app, Expr.Prop)
    print("✓ check((λx:Prop.x) A, Prop) = True")
    
    # Negative: Type ≢ Prop
    assert not tc.check(ctx, Expr.Type, Expr.Prop)
    print("✓ check(Type, Prop) = False")


def test_de_bruijn_operations():
    """de Bruijn 索引操作测试。"""
    print("\n=== de Bruijn Operations ===")
    env = Environment()
    reducer = Reducer(env)
    
    # instantiate: #0 -> val in body
    body = Expr.bvar(0)
    val = Expr.const(mk_name("V"))
    result = reducer.instantiate(body, val)
    assert result == val
    print("✓ instantiate(#0, V) = V")
    
    # instantiate: #1 -> val (should become #0)
    body2 = Expr.bvar(1)
    result2 = reducer.instantiate(body2, val)
    assert result2 == Expr.bvar(0)
    print("✓ instantiate(#1, V) = #0 (outer var shifted)")
    
    # instantiate: #0 stays #0 in λ body (λ binds new #0)
    lam_body = Expr.lam("y", Expr.Type, Expr.bvar(0))
    result3 = reducer.instantiate(lam_body, val)
    # The inner #0 refers to λ's binder, not the substituted value
    assert result3.kind.body == Expr.bvar(0)
    print("✓ instantiate(λy.#0, V) = λy.#0 (inner #0 preserved)")
    
    # lift: increment indices >= start
    expr = Expr.bvar(0)
    lifted = reducer.lift(expr, 0, 1)
    assert lifted == Expr.bvar(1)
    print("✓ lift(#0, 0, 1) = #1")
    
    # lift: only affect indices >= start
    expr2 = Expr.bvar(0)
    lifted2 = reducer.lift(expr2, 1, 1)
    assert lifted2 == Expr.bvar(0)  # #0 < 1, unchanged
    print("✓ lift(#0, 1, 1) = #0 (unaffected)")


def test_whnf_stack():
    """WHNF + 应用栈分解测试。"""
    print("\n=== WHNF Stack ===")
    env = Environment()
    reducer = Reducer(env)
    
    # Simple app
    f = Expr.const(mk_name("f"))
    a = Expr.const(mk_name("a"))
    app = Expr.app(f, a)
    head, args = reducer.whnf_stack(app)
    assert head == f
    assert args == [a]
    print("✓ whnf_stack(f a) = (f, [a])")
    
    # Nested app: ((f a) b)
    b = Expr.const(mk_name("b"))
    app2 = Expr.app(Expr.app(f, a), b)
    head2, args2 = reducer.whnf_stack(app2)
    assert head2 == f
    assert args2 == [a, b]
    print("✓ whnf_stack(f a b) = (f, [a, b])")
    
    # Reducible app: (λx.x) a → a
    id_fn = Expr.lam("x", Expr.Type, Expr.bvar(0))
    app3 = Expr.app(id_fn, a)
    head3, args3 = reducer.whnf_stack(app3)
    # After β-reduction, a is WHNF with no args
    assert head3 == a
    assert args3 == []
    print("✓ whnf_stack((λx.x) a) = (a, [])")


def run_all_tests():
    """运行所有测试。"""
    print("=" * 60)
    print("LeanPy 核心测试套件")
    print("=" * 60)
    
    test_beta_reduction()
    test_delta_reduction()
    test_zeta_reduction()
    test_whnf()
    test_definitional_equality()
    test_type_inference()
    test_type_checking()
    test_de_bruijn_operations()
    test_whnf_stack()
    
    print("\n" + "=" * 60)
    print("所有测试通过！")
    print("=" * 60)


if __name__ == "__main__":
    run_all_tests()
