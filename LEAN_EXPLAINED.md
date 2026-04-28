# Lean 定理证明器核心逻辑解析与 Python 复刻

> **项目**：LeanPy —— Lean 4 核心逻辑的 Python 复刻  
> **代码规模**：~5,900 行 Python  
> **核心概念**：Curry-Howard 同构、依赖类型理论、归纳构造演算

---

## 目录

1. [核心哲学：Curry-Howard 同构](#1-核心哲学curry-howard-同构)
2. [核心架构：表达式 AST](#2-核心架构表达式-ast)
3. [依赖类型系统](#3-依赖类型系统)
4. [宇宙层级](#4-宇宙层级)
5. [归纳类型与 Recursor](#5-归纳类型与-recursor)
6. [归约机制](#6-归约机制)
7. [类型检查器](#7-类型检查器)
8. [Tactic 系统](#8-tactic-系统)
9. [运行示例](#9-运行示例)

---

## 1. 核心哲学：Curry-Howard 同构

Lean 的根本洞见来自 **Curry-Howard 同构**（命题即类型，证明即程序）。

### 1.1 对应关系

| 逻辑层面 | 类型层面 | Lean 记号 | Python 复刻 |
|---------|---------|----------|------------|
| 命题 A | 类型 A | `A : Prop` | `Expr.sort(Level.PROP)` |
| 证明 t : A | 项 t : A | `t : A` | `check_type(ctx, t, A)` |
| A ∧ B (合取) | A × B (积类型) | `A ∧ B` | `Prod A B` |
| A ∨ B (析取) | A ⊕ B (和类型) | `A ∨ B` | `Sum A B` |
| A ⇒ B (蕴涵) | A → B (函数类型) | `A → B` | `arrow(A, B)` |
| ∀x:A. P(x) | Πx:A. P(x) (依赖函数) | `∀ x, P x` | `forallE("x", A, P)` |
| ⊥ (矛盾) | Empty (空类型) | `False` | `Empty` |
| ⊤ (真) | Unit (单元类型) | `True` | `Unit` |

### 1.2 核心洞察

```
要证明 A → B，就构造一个函数 λx. ...，它将 A 的证明转换为 B 的证明

在 LeanPy 中：
  proof = lam("x", A, body)    -- λ x : A. body
  type  = arrow(A, B)           -- A → B
  
类型检查器验证：check(ctx, proof, type) == True
```

### 1.3 为什么这很重要

**证明检查 = 类型检查**。在 Lean 的 kernel 中，不存在独立的"证明检查器"——唯一的判断形式是 `Γ ⊢ t : A`。当 `A` 是一个命题（`A : Prop`）时，`t : A` 就意味着 `t` 是 `A` 的一个证明。

```python
# LeanPy 中，证明检查就是类型检查
def check_proof(env, ctx, proof, prop):
    """检查 proof 是否是 prop 的有效证明"""
    return check_type(env, ctx, proof, prop)  # 就是类型检查！
```

---

## 2. 核心架构：表达式 AST

Lean 的所有内容——类型、项、命题、证明——都统一为 **`Expr`**（表达式）。

### 2.1 AST 定义

```python
@dataclass(frozen=True)
class Expr:
    """Lean 核心表达式——Curry-Howard 同构的载体"""
    kind: Union[
        BVar,      # 绑定变量（de Bruijn 索引）
        FVar,      # 自由变量（局部常量）
        MVar,      # 元变量（待填充的"洞"）
        Sort,      # 宇宙层级（Prop, Type, ...）
        Const,     # 全局常量引用
        App,       # 函数应用
        Lam,       # λ 抽象
        ForallE,   # Π 类型（依赖函数类型）
        LetE,      # let 绑定
        Lit,       # 字面量
    ]
```

### 2.2 de Bruijn 索引

Lean 使用 **de Bruijn 索引**表示绑定变量，避免 α-转换问题：

```
λ x : A. λ y : B. x    →    lam(A, lam(B, bvar 1))
                                    ^^^^
                                    x 是外层的第1个绑定（从0开始数）
```

**Python 实现**：
```python
# λ x : Nat. x  =>  lam(Nat, bvar 0)
id_term = Expr.lam("x", Expr.const(mk_name("Nat")), Expr.bvar(0))

# λ x : Nat. λ y : Bool. x  =>  lam(Nat, lam(Bool, bvar 1))
nested = Expr.lam("x", nat,
            Expr.lam("y", bool, Expr.bvar(1)))
```

### 2.3 构造示例

| Lean 语法 | Python 复刻 | 含义 |
|----------|------------|------|
| `Nat → Bool` | `arrow(nat, bool)` | 函数类型 |
| `∀ A : Type, A → A` | `forallE("A", Type, arrow(A, A))` | 多态恒等函数类型 |
| `λ x : Nat, x` | `lam("x", nat, bvar(0))` | 恒等函数 |
| `f a b` | `app(app(f, a), b)` | 多参数应用 |

---

## 3. 依赖类型系统

### 3.1 Π 类型（依赖函数类型）

**Π x : A. B(x)** 是普通函数类型 `A → B` 的泛化：返回类型 `B` 可以**依赖于**输入值 `x`。

```
普通函数：  f : Nat → Bool        -- 返回类型固定为 Bool
依赖函数：  g : Π n : Nat, Vec n  -- 返回类型依赖于 n
```

**逻辑对应**：`Π x : A. B(x)` = `∀ x : A, B(x)`（全称量词）

**Python 实现**：
```python
# Π A : Type. A → A   （多态恒等函数的类型）
poly_id_type = Expr.forallE("A", Expr.Type,
                    Expr.mk_arrow(Expr.bvar(0), Expr.bvar(0)))
```

### 3.2 替换与提升

依赖类型系统的核心操作是**替换**（instantiate）和**提升**（lift）：

```python
# 替换：将 de Bruijn 索引 #idx 替换为值 val
def instantiate(e: Expr, val: Expr, idx: int = 0) -> Expr:
    match e.kind:
        case Expr.BVar(i):
            if i == idx:
                return val          # 替换匹配变量
            elif i > idx:
                return Expr.bvar(i - 1)  # 越过被替换的绑定
            else:
                return e             # 不受影响的绑定
        case Expr.Lam(name, dtype, body):
            return Expr.lam(name, 
                instantiate(dtype, val, idx),
                instantiate(body, lift(val, 0, 1), idx + 1))
        # ... 其他情况

# 提升：增加绑定变量的索引
def lift(e: Expr, start_idx: int, num: int) -> Expr:
    # 将 e 中索引 >= start_idx 的变量索引增加 num
    ...
```

---

## 4. 宇宙层级

Lean 通过**宇宙层级**（Universe Hierarchy）避免 Girard 悖论。

### 4.1 层级结构

```
Sort 0 = Prop       -- 命题宇宙（proof irrelevant）
Sort 1 = Type 0     -- 小类型宇宙
Sort 2 = Type 1     -- 大类型宇宙
Sort 3 = Type 2     -- 更大类型宇宙
  ...
```

### 4.2 Prop 的特殊性：Proof Irrelevance

在 `Prop` 中，**所有证明都是等价的**：

```python
# 两个不同的证明 of 1+1=2，在核心层定义上等价
proof1 = rfl          -- 直接自反证明
proof2 = symm(symm(rfl))  -- 两次对称后再自反

# 在 Prop 中：proof1 ≡ proof2（定义等价）
# 在 Type 中：这两个项不相等
```

这使得 `Prop` 是 **impredicative** 的：一个 `Prop` 可以通过量化 `Type` 上的所有元素来定义。

### 4.3 imax 规则

```python
def imax(u: Level, v: Level) -> Level:
    """
    imax(u, v) = 0      如果 v = 0 (即 Prop)
                max(u, v) 否则
    
    这保证了：如果 B : Prop，则 Π x:A. B : Prop
    这是 impredicativity 的关键！
    """
    if v.is_zero():
        return Level.zero()
    return Level.max_level(u, v)
```

---

## 5. 归纳类型与 Recursor

### 5.1 归纳定义

归纳类型通过**构造器**（introduction rules）定义：

```lean
-- 自然数
definition: Nat
  constructors:
    Nat.zero : Nat
    Nat.succ : Nat → Nat
```

**Python 复刻**：
```python
nat_ind, nat_constants = mk_nat_type()
# Nat : Type
# Nat.zero : Nat
# Nat.succ : Nat → Nat
```

### 5.2 Recursor（自动生成的消去子）

Lean 自动为每个归纳类型生成 **recursor**（消去子/归纳原理）：

```lean
-- Nat.rec : 数学归纳法的类型论基础
Nat.rec : Π {motive : Nat → Sort u},
  motive zero →                                    -- 基础步
  (Π (n : Nat), motive n → motive (succ n)) →    -- 归纳步
  Π (t : Nat), motive t                           -- 结论
```

**Python 自动生成**：
```python
rec = generate_recursor(nat_ind)
# rec.name = "Nat.rec"
# rec.type = Π motive. motive zero → (Π n, motive n → motive (succ n)) → Π t, motive t
# rec.rules[0]: Nat.zero ↦ #0        (zero 分支取基础值)
# rec.rules[1]: Nat.succ ↦ (#1 #0)   (succ 分支应用归纳假设)
```

### 5.3 内置类型

| 类型 | 构造器 | 逻辑含义 |
|------|--------|---------|
| `Nat` | `zero`, `succ` | 自然数 |
| `Bool` | `false`, `true` | 布尔值 |
| `Unit` | `unit` | 真命题 ⊤ |
| `Empty` | （无） | 假命题 ⊥ |
| `Prod A B` | `mk` | 合取 A ∧ B |
| `Sum A B` | `inl`, `inr` | 析取 A ∨ B |

---

## 6. 归约机制

Lean 的 kernel 在类型检查中执行四种归约，定义**定义等价**（definitional equality）。

### 6.1 四种归约

| 归约 | 规则 | 示例 |
|------|------|------|
| **β** | `(λx.t) a → t[a/x]` | `(λx.x) 5 → 5` |
| **δ** | 展开定义 | `double 5 → 5 + 5` |
| **ι** | 归纳类型计算 | `Nat.rec C z s (succ n) → s n (Nat.rec C z s n)` |
| **ζ** | let 绑定消去 | `let x:=t in s → s[t/x]` |

### 6.2 弱头范式（WHNF）

Lean 的类型检查器只归约到**弱头范式**（最外层不可再归约）：

```python
def whnf(self, e: Expr) -> Expr:
    """将表达式归约到弱头范式"""
    while True:
        e = instantiate_mvars(e)
        
        # β-归约: (λx.t) a
        if is_beta_redex(e):
            e = beta_reduce(e)
            continue
            
        # ζ-归约: let x:=t in s
        if e.is_letE():
            e = zeta_reduce(e)
            continue
            
        # δ-归约: 展开定义
        if is_delta_redex(e):
            e = delta_reduce(e)
            continue
            
        # ι-归约: recursor 计算
        if is_iota_redex(e):
            e = iota_reduce(e)
            continue
            
        return e  # WHNF  reached
```

### 6.3 定义等价

两个项定义等价，当且仅当它们通过 β/δ/ι/ζ 归约可变为相同项：

```python
def is_def_eq(self, t1: Expr, t2: Expr) -> bool:
    """判断 t1 和 t2 是否定义等价"""
    # 快速路径
    if t1 == t2:
        return True
    
    # 归约到 WHNF
    t1_whnf = self.whnf(t1)
    t2_whnf = self.whnf(t2)
    
    if t1_whnf == t2_whnf:
        return True
    
    # 递归比较结构
    match (t1_whnf.kind, t2_whnf.kind):
        case (Expr.Lam(_, d1, b1), Expr.Lam(_, d2, b2)):
            return is_def_eq(d1, d2) and is_def_eq(b1, b2)
        case (Expr.ForallE(_, d1, b1), Expr.ForallE(_, d2, b2)):
            return is_def_eq(d1, d2) and is_def_eq(b1, b2)
        case (Expr.App(f1, a1), Expr.App(f2, a2)):
            return is_def_eq(f1, f2) and is_def_eq(a1, a2)
        # ... 其他情况
```

---

## 7. 类型检查器

### 7.1 类型推断（核心算法）

```python
def infer(self, ctx: LocalContext, e: Expr) -> Expr:
    """推断 e 在上下文 ctx 中的类型"""
    match e.kind:
        case Expr.BVar(idx):
            # VAR: 从局部上下文获取类型
            return ctx.get_type(idx)
        
        case Expr.Const(name, levels):
            # CONST: 从环境获取并实例化 universe
            info = self.env.lookup(name)
            return instantiate_levels(info.type, levels)
        
        case Expr.Sort(level):
            # SORT: Sort u : Sort (u+1)
            return Expr.sort(Level.succ(level))
        
        case Expr.App(fn, arg):
            # APP: 检查函数类型，替换参数
            fn_type = self.infer(ctx, fn)
            pi_type = self.reducer.whnf(fn_type)
            self.check(ctx, arg, pi_type.kind.dtype)
            return instantiate(pi_type.kind.body, arg)
        
        case Expr.Lam(name, dtype, body):
            # LAM: 扩展上下文，推断 body 类型，返回 Π 类型
            new_ctx = ctx.extend(name, dtype)
            body_type = self.infer(new_ctx, body)
            return Expr.forallE(name, dtype, body_type)
        
        case Expr.ForallE(name, dtype, body):
            # PI: 推断 Π x:A. B 的类型 = Sort(imax u v)
            u = self.ensure_sort(ctx, dtype)
            new_ctx = ctx.extend(name, dtype)
            v = self.ensure_sort(new_ctx, body)
            return Expr.sort(imax(u, v))
        
        case Expr.LetE(name, dtype, value, body):
            # LET: 检查 value，扩展 let 上下文
            self.check(ctx, value, dtype)
            new_ctx = ctx.extend_let(name, dtype, value)
            body_type = self.infer(new_ctx, body)
            return instantiate(body_type, value)
```

### 7.2 类型检查

```python
def check(self, ctx, e: Expr, expected: Expr) -> bool:
    """检查 e 是否具有类型 expected"""
    inferred = self.infer(ctx, e)
    return self.is_def_eq(inferred, expected)
```

---

## 8. Tactic 系统

### 8.1 架构

Tactic 是**帮助用户构造证明项的交互式工具**。最终的 proof term 仍通过 kernel 的类型检查。

```
用户（Tactic 语法）
  ↓
Tactic State（元变量管理）
  ↓
核心项（Kernel Term）
  ↓
Kernel 类型检查
```

### 8.2 核心组件

```python
@dataclass
class Goal:
    """证明目标 = 待证的元变量"""
    mvar_id: int           # 元变量 ID
    local_ctx: LocalContext  # 可用假设
    target: Expr           # 待证明的命题

@dataclass
class ProofState:
    """证明状态"""
    goals: List[Goal]      # 待解决目标列表
    metavar_ctx: MetavarContext
    env: Environment
```

### 8.3 基本 Tactics

| Tactic | 功能 | 逻辑含义 |
|--------|------|---------|
| `intro x` | 从 A → B 引入假设 A | λ 抽象 |
| `apply f` | 用 f : A → B 匹配目标 B | 函数应用 |
| `exact t` | 直接提供证明项 t | 直接构造 |
| `assumption` | 在上下文中查找匹配假设 | 自动完成 |
| `rewrite h` | 用等式 h 重写目标 | 等式替换 |

### 8.4 证明示例

```python
# 证明 A → A
state = start_proof(env, arrow(nat, nat))  # 目标: ⊢ Nat → Nat
state = Intro("n").run(state)               # n : Nat ⊢ Nat
state = Assumption().run(state)             # 解决！
proof = finish_proof(state)                 # 获取证明项: λ n : Nat. n
```

---

## 9. 运行示例

### 9.1 恒等函数（A → A）

```
项    : λ A : Type. λ x : A. x
类型  : Π A : Type. A → A
含义  : 每个命题都蕴涵自身（自反性）
```

### 9.2 K 组合子（A → B → A）

```
项    : λ A B : Type. λ a : A. λ b : B. a
类型  : Π A B : Type. A → B → A
含义  : 前件加强律——如果 A 成立，那么无论 B 如何，A 都成立
```

### 9.3 自然数定义

```
Nat : Type
├── Nat.zero : Nat              （零）
└── Nat.succ : Nat → Nat        （后继）

Nat.rec : Π motive. motive zero → (Π n, motive n → motive (succ n)) → Π t, motive t
        （数学归纳法的类型论基础）
```

### 9.4 Curry-Howard 总结

```
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
╠═══════════════════════╬═══════════════════════╣
║  intro (引入假设)      ║  λ 抽象               ║
║  apply (应用定理)      ║  函数应用             ║
║  exact (直接证明)      ║  直接构造项            ║
╚═══════════════════════╩═══════════════════════╝
```

---

## 项目文件结构

```
leanpy/
├── __init__.py      # 模块入口
├── name.py          # 分层名称系统 (106 行)
├── level.py         # 宇宙层级系统 (194 行)
├── expr.py          # 核心表达式 AST (384 行)
├── environment.py   # 全局环境 + 局部上下文 (638 行)
├── inductive.py     # 归纳类型 + Recursor 生成 (472 行)
├── reducer.py       # β/δ/ι/ζ 归约 + WHNF (804 行)
├── typechecker.py   # 类型推断 + 类型检查 (933 行)
├── parser.py        # 类 Lean 语法解析器 (657 行)
├── tactic.py        # 交互式 Tactic 系统 (609 行)
├── examples.py      # 完整示例证明 (689 行)
└── test_core.py     # 核心测试套件 (370 行)

LEAN_EXPLAINED.md    # 本文档
lean_core_structure.md # 深度技术研究报告
```

---

## 关键设计决策

1. **de Bruijn 索引**：所有绑定变量使用数字索引而非名称，消除 α-转换的复杂性
2. **函数式更新**：Environment 和 LocalContext 返回新对象，便于回溯
3. **WHNF 策略**：类型检查只归约到最外层，保证效率
4. **元变量机制**：Tactic 系统基于"待填充的洞"构建，与 Lean 4 架构一致
5. **Recursor 自动生成**：从归纳类型定义自动推导消去子和计算规则

## 局限与简化

1. **Universe 累积性**：未实现完整的 universe cumulativity
2. **Higher-order Unification**：元变量求解是简化版本
3. **类型类（Type Classes）**：未实现
4. **归纳族的复杂递归**：参数化/索引族的处理做了简化

## 参考

- [The Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Type Theory and Formal Proof](https://www.cambridge.org/core/books/type-theory-and-formal-proof/).
- [Homotopy Type Theory Book](https://homotopytypetheory.org/book/)
