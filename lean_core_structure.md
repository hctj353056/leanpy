# Lean 4 核心逻辑结构：深入技术报告

> 本报告旨在精确阐述 Lean 4 定理证明器的底层逻辑机制，为 Python 实现提供形式化参考。

---

## 目录

1. [基础哲学：Curry-Howard 同构](#1-基础哲学curry-howard-同构)
2. [核心演算：带类型的 λ 演算扩展](#2-核心演算带类型的-λ-演算扩展)
3. [依赖类型系统](#3-依赖类型系统)
4. [宇宙层级（Sort/Type/Prop）](#4-宇宙层级sorttypeprop)
5. [归纳类型（Inductive Types）](#5-归纳类型inductive-types)
6. [定义环境（Environment）](#6-定义环境environment)
7. [归约机制](#7-归约机制)
8. [Tactic 系统基础](#8-tactic-系统基础)
9. [形式化规则汇总](#9-形式化规则汇总)

---

## 1. 基础哲学：Curry-Howard 同构

### 1.1 核心命题：命题即类型，证明即程序

Curry-Howard 同构（Curry-Howard correspondence / proofs-as-programs correspondence）揭示了逻辑系统与计算系统之间的深层同构关系：

| 逻辑层面 | 类型层面 | Lean 记号 |
|---------|---------|----------|
| 命题（Proposition） | 类型（Type） | `P : Prop` |
| 证明（Proof） | 程序/项（Term） | `p : P` |
| 蕴涵 $A \Rightarrow B$ | 函数类型 $A \to B$ | `A → B` |
| 合取 $A \land B$ | 积类型 $A \times B$ | `A ∧ B` |
| 析取 $A \lor B$ | 和类型 $A \oplus B$ | `A ∨ B` |
| 全称量词 $\forall x:A, P(x)$ | 依赖函数类型 $\Pi x:A, P(x)$ | `∀ x : A, P x` |
| 存在量词 $\exists x:A, P(x)$ | 依赖对类型 $\Sigma x:A, P(x)$ | `∃ x : A, P x` |
| 真（$\top$） | 单位类型（Unit） | `True` |
| 假（$\bot$） | 空类型（Void） | `False` |

**核心洞察**：一个命题 $P$ 为真，当且仅当存在类型为 $P$ 的项（即存在一个证明）。证明检查就是类型检查。

### 1.2 形式化解释

在 Lean 中，上下文 $\Gamma$ 是一个假设列表，每个假设形如 $x : A$，表示"假设 $x$ 是类型 $A$ 的一个项"。

判断（judgment）的形式为：

$$\Gamma \vdash t : A$$

读作："在上下文 $\Gamma$ 中，项 $t$ 具有类型 $A$"。当 $A : \text{Prop}$ 时，这等价于说"$t$ 是命题 $A$ 的一个证明"。

### 1.3 用 λ 项证明 $A \to B$

**逻辑层面**：要证明 $A \Rightarrow B$，我们需要"假设 $A$ 成立，然后推出 $B$"。

**类型层面**：要构造一个类型为 $A \to B$ 的项，我们需要一个函数，它接收类型为 $A$ 的输入，返回类型为 $B$ 的输出。

**具体例子**：

```lean
-- 证明 A → A（自反蕴涵）
def id_proof (A : Prop) (a : A) : A := a

-- 其类型为：∀ A : Prop, A → A
-- 对应的 λ 项（核心层）：λ A : Prop. λ a : A. a
```

形式化地：

$$\vdash \lambda A : \text{Prop}. \lambda a : A. a : \prod_{A : \text{Prop}} A \to A$$

更经典的例子：证明 $A \to (B \to A)$（蕴涵的前件加强律/K 组合子）：

```lean
def K (A B : Prop) (a : A) (b : B) : A := a
-- λ 项：λ A B : Prop. λ a : A. λ b : B. a
-- 类型：∀ A B : Prop, A → B → A
```

形式化为：

$$\vdash \lambda A B : \text{Prop}. \lambda a : A. \lambda b : B. a : \prod_{A : \text{Prop}} \prod_{B : \text{Prop}} A \to B \to A$$

### 1.4 证明检查与类型检查的等价性

在 Lean 的核心层（kernel），不存在独立的"证明检查器"。唯一存在的判断形式是：

$$\Gamma \vdash t : A$$

**证明检查 = 类型检查**：

- 要检查 $t$ 是否是命题 $P$ 的证明，kernel 检查 $t : P$ 是否成立
- 类型推导算法同时完成了"证明是否正确"的验证
- 这是 Curry-Howard 同构在工程实现上的直接体现

**重要推论**：

1. 如果一个命题 $P$ 不可证明（即不存在闭合项 $t$ 使得 $\vdash t : P$），那么 $P$ 在逻辑上不可证。
2. 类型系统的健全性（soundness）等价于逻辑系统的一致性（consistency）。
3. 类型检查终止性保证了证明检查的可判定性。

### 1.5 Python 实现视角

```python
# 核心判断的数据结构
class Judgment:
    """Γ ⊢ t : A"""
    def __init__(self, context: Context, term: Term, typ: Term):
        self.context = context  # 局部上下文
        self.term = term        # 项 t
        self.typ = typ          # 类型 A

# 证明检查就是类型检查
def check_proof(env: Environment, ctx: Context, proof: Term, prop: Term) -> bool:
    """检查 proof 是否是 prop 的一个有效证明"""
    return check_type(env, ctx, proof, prop)  # 就是类型检查！
```

---

## 2. 核心演算：带类型的 λ 演算扩展

### 2.1 抽象语法树（AST）定义

Lean 核心层的项（term）由以下语法生成：

$$\begin{aligned}
t, s, A, B ::=\ & x \quad &&\text{(变量/局部常量)} \\
& \mid c \quad &&\text{(全局常量：定义、公理、归纳类型等)} \\
& \mid s \quad &&\text{(sort/universe：Prop, Type u, Sort u)} \\
& \mid \lambda x : A.\, t \quad &&\text{(λ 抽象 / 函数引入)} \\
& \mid \Pi x : A.\, B \quad &&\text{(依赖函数类型 / Π 类型)} \\
& \mid t\, s \quad &&\text{(函数应用)} \\
& \mid \text{let } x : A := t \text{ in } s \quad &&\text{(let 绑定)} \\
& \mid \text{recursor}_C\, t\, u_1 \ldots u_n \quad &&\text{(归纳类型的消去子)}
& \end{aligned}$$

其中：
- $x$ 表示局部变量（de Bruijn 索引或命名变量）
- $c$ 表示全局常量，指向环境（environment）中的声明
- $s$ 表示宇宙层级（Sort 0 = Prop, Sort 1 = Type 0, ...）

**Lean 4 内部 AST（简化版）**：

```
Expr ::=
  | bvar deBruijnIndex          -- 绑定变量（de Bruijn 索引）
  | fvar FVarId                  -- 自由变量（唯一 ID）
  | mvar MVarId                  -- 元变量（待填充的"洞"）
  | sort Level                   -- 宇宙层级
  | const Name LevelList         -- 全局常量（含 universe 参数）
  | app Expr Expr                -- 应用
  | lam Name Expr Expr BinderInfo -- λ 抽象: λ (x : A). B
  | forallE Name Expr Expr BinderInfo -- Π 类型: Π (x : A). B
  | letE Name Expr Expr Expr Bool -- let x : A := t in s
  | lit Literal                  -- 字面量（自然数、字符串）
  | mdata MData Expr             -- 元数据
  | proj Name Nat Expr           -- 投影（结构体字段访问）
```

### 2.2 de Bruijn 索引

Lean 核心层使用 de Bruijn 索引表示绑定变量，避免 α-转换问题：

- $\lambda x : A.\, t$ 中，$x$ 在 $t$ 中被替换为数字索引
- 索引 $n$ 表示"向外数第 $n$ 个 λ/Π/let 绑定"
- 例如：$\lambda x : A.\, \lambda y : B.\, x$ 写作 $\lambda A.\, \lambda B.\, \#1$

**替换（substitution）的精确定义**：

令 $t[s/n]$ 表示将 $t$ 中的第 $n$ 个绑定变量替换为 $s$：

$$\begin{aligned}
\#m[s/n] &= \begin{cases} s & m = n \\ \#m & m < n \\ \#(m-1) & m > n \end{cases} \\
(c)[s/n] &= c \quad \text{（全局常量不变）} \\
(u\, v)[s/n] &= u[s/n]\, v[s/n] \\
(\lambda A.\, t)[s/n] &= \lambda A[s/n].\, t[s/(n+1)] \\
(\Pi A.\, B)[s/n] &= \Pi A[s/n].\, B[s/(n+1)] \\
(\text{let } A := t \text{ in } u)[s/n] &= \text{let } A[s/n] := t[s/n] \text{ in } u[s/(n+1)]
\end{aligned}$$

### 2.3 α-转换

使用 de Bruijn 索引后，α-等价（alpha-equivalence）变为语法上的数字等价：

$$\lambda x : A.\, t \equiv_\alpha \lambda y : A.\, t[y/x] \quad \Longleftrightarrow \quad \text{两者的 de Bruijn 表示完全相同}$$

**判断 $t \equiv_\alpha s$ 的算法**：

```python
def alpha_eq(t: Expr, s: Expr) -> bool:
    """检查两个 Expr 是否 α-等价（在 de Bruijn 表示下就是结构相等）"""
    # 如果内部使用 de Bruijn 索引，α-等价 = 结构递归相等
    match (t, s):
        case (BVar(n1), BVar(n2)): return n1 == n2
        case (FVar(id1), FVar(id2)): return id1 == id2
        case (Sort(l1), Sort(l2)): return level_eq(l1, l2)
        case (Const(n1, ls1), Const(n2, ls2)): return n1 == n2 and ls1 == ls2
        case (App(f1, a1), App(f2, a2)): return alpha_eq(f1, f2) and alpha_eq(a1, a2)
        case (Lam(_, d1, b1, _), Lam(_, d2, b2, _)): 
            return alpha_eq(d1, d2) and alpha_eq(b1, b2)
        case (ForallE(_, d1, b1, _), ForallE(_, d2, b2, _)):
            return alpha_eq(d1, d2) and alpha_eq(b1, b2)
        case (LetE(_, t1, v1, b1, _), LetE(_, t2, v2, b2, _)):
            return alpha_eq(t1, t2) and alpha_eq(v1, v2) and alpha_eq(b1, b2)
        case _: return False
```

### 2.4 Typing Rules（推理规则）

使用 sequent 形式写出核心类型规则。判断形式：$\Gamma \vdash t : A$，其中 $\Gamma$ 是上下文（有序的假设列表 $x_1 : A_1, \ldots, x_n : A_n$）。

**变量规则**：

$$\frac{(x : A) \in \Gamma}{\Gamma \vdash x : A} \quad \text{(VAR)}$$

**全局常量规则**：

$$\frac{(c : A) \in \text{Env}}{\Gamma \vdash c : A} \quad \text{(CONST)}$$

**Sort 规则**（宇宙层级）：

$$\frac{}{\Gamma \vdash \text{Sort}\, u : \text{Sort}\, (u+1)} \quad \text{(SORT)}$$

在 Lean 中：
- $\text{Prop} = \text{Sort}\, 0$
- $\text{Type}\, u = \text{Sort}\, (u+1)$

**Π 类型形成规则**：

$$\frac{\Gamma \vdash A : \text{Sort}\, u \quad \Gamma, x : A \vdash B : \text{Sort}\, v}
      {\Gamma \vdash \Pi x : A.\, B : \text{Sort}\, (\text{imax}\, u\, v)} \quad \text{(PI-FORM)}$$

其中 $\text{imax}\, u\, v$ 定义为：如果 $v = 0$ 则 $0$，否则 $\max(u, v)$。这保证了如果 $B : \text{Prop}$，则 $\Pi x : A.\, B : \text{Prop}$（这是 impredicativity 的关键）。

**λ 抽象规则**：

$$\frac{\Gamma, x : A \vdash t : B \quad \Gamma \vdash \Pi x : A.\, B : s}
      {\Gamma \vdash \lambda x : A.\, t : \Pi x : A.\, B} \quad \text{(LAM)}$$

**应用规则**：

$$\frac{\Gamma \vdash f : \Pi x : A.\, B \quad \Gamma \vdash a : A}
      {\Gamma \vdash f\, a : B[a/x]} \quad \text{(APP)}$$

**let 绑定规则**：

$$\frac{\Gamma \vdash t : A \quad \Gamma, x : A \vdash s : B \quad \Gamma \vdash B : \text{Sort}\, u}
      {\Gamma \vdash \text{let } x : A := t \text{ in } s : B[t/x]} \quad \text{(LET)}$$

**转换规则（Conversion）**：

$$\frac{\Gamma \vdash t : A \quad \Gamma \vdash B : s \quad A \equiv_\beta B}
      {\Gamma \vdash t : B} \quad \text{(CONV)}$$

其中 $A \equiv_\beta B$ 表示 $A$ 和 $B$ 在 β-归约（以及 δ, ι, ζ 归约）下可互相转换。这是 Curry-Howard 同构中"证明无关性"的技术基础。

---

## 3. 依赖类型系统

### 3.1 Π-types（依赖函数类型）

**直观理解**：

普通函数类型 $A \to B$ 的返回类型 $B$ 不依赖于输入值。依赖函数类型 $\Pi x : A.\, B(x)$ 的返回类型 $B$ **可以依赖于**输入值 $x$。

**形式定义**：

$$\Pi x : A.\, B(x) = \{ f \mid \forall x : A,\, f(x) : B(x) \}$$

**例子——向量长度类型**：

```lean
-- Vec A n 表示长度为 n 的 A-向量
inductive Vec (A : Type) : Nat → Type where
  | nil : Vec A 0
  | cons : A → {n : Nat} → Vec A n → Vec A (n+1)

-- 依赖函数：保证输出向量长度 = 输入 + 1
-- 类型为: ∀ n : Nat, Vec Nat n → Vec Nat (n+1)
def addOne (n : Nat) (v : Vec Nat n) : Vec Nat (n + 1) :=
  Vec.cons 1 v
```

这里 `addOne` 的类型是 $\Pi n : \text{Nat}.\, \text{Vec}\, \text{Nat}\, n \to \text{Vec}\, \text{Nat}\, (n+1)$，返回类型依赖于输入 $n$。

**逻辑对应**：

| 依赖函数类型 | 逻辑命题 |
|------------|---------|
| $\Pi x : A.\, B(x)$ | $\forall x : A,\, B(x)$ |

证明 $\Pi x : A.\, B(x)$ 就是构造一个函数，对任意 $x : A$ 返回 $B(x)$ 的证明。

**核心实现机制（Python 视角）**：

```python
@dataclass
class Pi:
    """Π x : A. B"""
    name: str        # 绑定变量名（用于显示）
    domain: Expr     # A
    body: Expr       # B（内部 de Bruijn 索引引用 x）
    
def check_pi(env, ctx, e: Pi):
    # 检查 A 是合法的 sort
    u = check_type(env, ctx, e.domain)
    # 扩展上下文
    ctx_ext = ctx.extend(e.name, e.domain)
    # 检查 B 在扩展上下文中是合法的 sort
    v = check_type(env, ctx_ext, e.body)
    # 返回 imax(u, v)
    return Sort(imax(u, v))
```

### 3.2 Σ-types（依赖对类型）

**直观理解**：

$\Sigma x : A.\, B(x)$ 表示满足 $B(x)$ 的 $x : A$ 的"配对"$(x, p)$，其中 $p : B(x)$。

**形式定义**：

```lean
-- Lean 中的 Σ 类型定义
structure Sigma {A : Type u} (B : A → Type v) where
  fst : A
  snd : B fst
```

**逻辑对应**：

| 依赖对类型 | 逻辑命题 |
|-----------|---------|
| $\Sigma x : A.\, B(x)$ | $\exists x : A,\, B(x)$ |

证明 $\Sigma x : A.\, B(x)$ 就是构造一个具体的见证（witness）$a : A$ 和 $b : B(a)$。

**注意**：Lean 使用 `∃` 表示存在量词，其底层是一个结构体（structure），本质上就是 Σ-type：

```lean
-- ∃ x : A, P x 是 Sigma (fun x => P x) 的简写
def exists.intro {A : Type} {P : A → Prop} (a : A) (h : P a) : ∃ x, P x :=
  ⟨a, h⟩
```

### 3.3 依赖类型与普通类型的关键区别

| 特性 | 普通类型 $A \to B$ | 依赖类型 $\Pi x : A.\, B(x)$ |
|------|-------------------|---------------------------|
| 返回类型 | 固定为 $B$ | 依赖于输入值 $x$ |
| 类型检查 | $f(a) : B$ | $f(a) : B[a/x]$（需要代入） |
| 逻辑含义 | 蕴涵 $A \Rightarrow B$ | 全称量词 $\forall x, B(x)$ |
| 计算含义 | 普通函数 | 依赖函数 |
| 类型等价 | $A \to B = A' \to B'$ 当 $A=A', B=B'$ | $\Pi x:A. B(x) = \Pi x:A'. B'(x)$ 需要逐点等价 |

**关键区别：类型检查时需要计算（evaluation）**

在依赖类型系统中，类型检查可能需要对项进行归约：

```lean
def f (n : Nat) : Vec Nat (n + 0) → Vec Nat n :=
  fun v => v  -- 需要知道 n + 0 = n
```

这里类型 `Vec Nat (n + 0)` 和 `Vec Nat n` 在定义上不同，但通过 β/δ/ι-归约等价。Kernel 必须能够在类型检查过程中执行归约。

### 3.4 Universe Polymorphism（宇宙多态）

Lean 支持 universe polymorphism，允许定义对任意 universe 层级都适用的构造：

```lean
def id.{u} (A : Type u) (a : A) : A := a
--        ^^^ universe 参数
```

形式化地，id 的类型为：

$$\vdash \text{id} : \prod_{u : \text{Level}} \prod_{A : \text{Type}\, u} A \to A$$

**宇宙层级表达式（Level）的语法**：

$$\ell ::= 0 \mid 1 \mid 2 \mid \ldots \mid u \mid \ell + 1 \mid \max(\ell_1, \ell_2) \mid \text{imax}(\ell_1, \ell_2)$$

其中 $u$ 是 universe 变量。在实例化时，每个 universe 参数被替换为具体的层级表达式。

---

## 4. 宇宙层级（Sort/Type/Prop）

### 4.1 基本层级结构

Lean 的宇宙系统采用累积层级（cumulative hierarchy）：

```
Sort 0  = Prop      -- 不可证伪的命题宇宙（proof irrelevant）
Sort 1  = Type 0    -- 小类型宇宙（通常记作 Type）
Sort 2  = Type 1    -- 大类型宇宙
Sort 3  = Type 2    -- 更大类型宇宙
  ...
```

一般规则：$\text{Sort}\, u : \text{Sort}\, (u+1)$

### 4.2 Prop：证明无关性（Proof Irrelevance）

**核心性质**：对于任意 $P : \text{Prop}$ 和任意两个证明 $p, q : P$，有 $p = q$（定义上相等）。

形式化声明：

$$\frac{\Gamma \vdash p : P \quad \Gamma \vdash q : P \quad \Gamma \vdash P : \text{Prop}}
      {\Gamma \vdash p \equiv q : P} \quad \text{(PROOF-IRRELEVANCE)}$$

**含义与影响**：

1. **不区分具体证明**：所有 $P$ 的证明在计算中被视为等价
2. **提取（Extraction）**：证明可以被安全地擦除，不影响程序运行
3. **逻辑与计算的分离**：Prop 层用于逻辑，Type 层用于计算

```lean
-- 在 Prop 中，两个证明定义上相等
def proof1 : 1 + 1 = 2 := rfl
def proof2 : 1 + 1 = 2 := Eq.symm (Eq.symm rfl)

-- proof1 和 proof2 在核心层是定义上相等的！
-- 这在 Type 层不成立
```

**impredicativity of Prop**：

如果 $B : \text{Prop}$，则无论 $A$ 在哪个 universe，都有 $(\Pi x : A.\, B) : \text{Prop}$。

这使得 Prop 是 **impredicative** 的：一个 Prop 可以通过量化 Type 上的所有元素来定义。

```lean
-- 这是合法的，因为结果在 Prop 中
def universal_prop (A : Type) (P : A → Prop) : Prop := ∀ x : A, P x
-- 返回类型是 Prop，尽管 A 可能在 Type u 中
```

### 4.3 Type 0, Type 1, Type 2 ... 的层级

**累积性（Cumulativity）**：

$$\frac{\Gamma \vdash t : \text{Type}\, u}{\Gamma \vdash t : \text{Type}\, (u+1)} \quad \text{(CUMULATIVITY)}$$

这意味着如果 $A : \text{Type}\, 0$，那么也有 $A : \text{Type}\, 1$。

**为什么需要累积性**：

```lean
def list_pair (A B : Type) : Type := List (A × B)
-- A 和 B 可能在 Type 0，但 A × B 也在 Type 0，List (A × B) 在 Type 0
```

如果没有累积性，就需要大量显式的 universe 提升（lift）操作。

### 4.4 Sort u 作为 Universe 变量

Universe 变量 $u$ 出现在以下上下文中：

```lean
-- universe 声明
universe u v w

-- universe polymorphic 定义
def map.{u, v} {A : Type u} {B : Type v} (f : A → B) : List A → List B
```

**形式化规则**：

$$\frac{\Gamma \vdash A : \text{Sort}\, u \quad u \leq v}
      {\Gamma \vdash A : \text{Sort}\, v} \quad \text{(UNIV-CUMUL)}$$

### 4.5 Girard 悖论与 Universe 层级的必要性

**Girard 悖论**（类似于 Russell 悖论和 Burali-Forti 悖论的类型论版本）：如果允许 $A : A$（类型包含自身），则系统不一致。

**如何避免**：通过 universe 层级，每个类型都生活在一个更高层级的 universe 中：

$$A : \text{Sort}\, u \Rightarrow A \notin \text{Sort}\, u$$

即没有任何类型是它自身的元素。具体地：

- $A : \text{Type}\, u$ 意味着 $A$ 的类型是 $\text{Type}\, (u+1)$，不是 $\text{Type}\, u$
- 这避免了自引用导致的悖论

**Lean 的处理**：

```lean
-- 非法！会导致 universe 冲突
def bad : Type := Type
-- error: universe level mismatch

-- 合法：Type : Type 1，Type 1 : Type 2，以此类推
check Type  -- Type 1
check Type 1 -- Type 2
```

### 4.6 宇宙层级约束求解

在 Lean 中，universe 参数在定义时生成约束，在实例化时求解：

```lean
def compose.{u, v, w} {A : Type u} {B : Type v} {C : Type w}
  (f : B → C) (g : A → B) : A → C := fun x => f (g x)

-- 使用时：universe 参数自动推断
#check compose (fun x : Nat => x + 1) (fun x : Int => Int.toNat x)
-- 会生成约束并求解 u, v, w
```

**约束形式**：
- $u = v$（等式约束）
- $u \leq v$（不等式约束）


---

## 5. 归纳类型（Inductive Types）

### 5.1 归纳定义的形式

Lean 中归纳类型的通用形式：

```lean
inductive I (p₁ : P₁) ... (pₙ : Pₙ) : Π (i₁ : A₁) ... (iₖ : Aₖ), Sort u where
  | c₁ : Π (x₁ : B₁) ... (xₘ : Bₘ), I p₁ ... pₙ a₁ ... aₖ
  | c₂ : ...
  | ...
```

其中：
- $p_1, \ldots, p_n$ 是**参数**（parameters）：在所有构造器和归纳类型的结果类型中保持一致
- $i_1, \ldots, i_k$ 是**索引**（indices）：在不同构造器中可以不同
- $c_1, c_2, \ldots$ 是**构造器**（constructors）

### 5.2 严格 positivity 条件

为了保证归纳类型的一致性（不产生悖论），每个构造器的参数必须满足**严格 positivity 条件**：

一个类型 $T$ 在 $I$ 中出现是**严格正**的，当：

1. $T$ 不包含 $I$（即 $T$ 与 $I$ 无关），或者
2. $T = \Pi x_1 : A_1. \ldots \Pi x_n : A_n.\, I\, t_1 \ldots t_k$，其中 $I$ 不出现在任何 $A_i$ 中

**禁止的例子**：

```lean
-- 非法！IndBad 出现在其构造器参数的非正位置
inductive IndBad where
  | mk : (IndBad → IndBad) → IndBad
-- error: arg #1 of IndBad.mk has a non positive occurrence of the datatypes being declared
```

这是因为非正归纳类型会导致 Girard 悖论式的自指，破坏系统一致性。

### 5.3 Nat, Bool, List 的定义方式

**自然数 Nat**：

```lean
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
```

形式化展开（核心层表示）：

- 参数：无
- 索引：无
- 构造器：$\text{zero} : \text{Nat}$，$\text{succ} : \text{Nat} \to \text{Nat}$

**布尔值 Bool**：

```lean
inductive Bool where
  | false : Bool
  | true : Bool
```

**列表 List**：

```lean
inductive List (A : Type u) where
  | nil : List A
  | cons : A → List A → List A
```

形式化展开：

- 参数：$A : \text{Type}\, u$
- 索引：无
- 构造器：
  - $\text{nil} : \Pi A : \text{Type}\, u.\, \text{List}\, A$
  - $\text{cons} : \Pi A : \text{Type}\, u.\, A \to \text{List}\, A \to \text{List}\, A$

### 5.4 索引族：Vec 的例子

```lean
inductive Vec (A : Type u) : Nat → Type u where
  | nil : Vec A 0
  | cons : A → {n : Nat} → Vec A n → Vec A (n+1)
```

形式化展开：

- 参数：$A : \text{Type}\, u$
- 索引：$n : \text{Nat}$
- 构造器：
  - $\text{nil} : \Pi A : \text{Type}\, u.\, \text{Vec}\, A\, 0$
  - $\text{cons} : \Pi A : \text{Type}\, u.\, \Pi n : \text{Nat}.\, A \to \text{Vec}\, A\, n \to \text{Vec}\, A\, (\text{succ}\, n)$

注意索引族中，构造器的返回类型中的索引可以不同（nil 返回 0，cons 返回 succ n）。

### 5.5 归纳原理（Induction Principle）

对于每个归纳类型，Lean 自动生成其**归纳原理**（也称为消去子 / eliminator / recursor）。

**Nat 的归纳原理**：

```lean
-- Nat.rec 的核心类型
Nat.rec : {motive : Nat → Sort u} →
  motive zero →
  ((n : Nat) → motive n → motive (succ n)) →
  (t : Nat) → motive t
```

形式化理解：

给定一个**动机**（motive，即要证明/构造的依赖类型）$P : \text{Nat} \to \text{Sort}\, u$，以及：
- $P(0)$ 的证明/元素
- 归纳步：$\forall n, P(n) \to P(n+1)$

则可以推出 $\forall t, P(t)$。

**核心层 recursor 的形式**：

对于归纳类型 $I$ 有构造器 $c_1, \ldots, c_n$，其 recursor 的形式为：

$$\text{rec}_I : \prod_{C : I\, p_1 \ldots p_n \to \text{Sort}\, u} \prod_{f_1 : T_1[C]} \ldots \prod_{f_n : T_n[C]} \prod_{t : I\, p_1 \ldots p_n} C\, t$$

其中 $T_i[C]$ 是构造器 $c_i$ 对应的归纳分支类型。

### 5.6 Recursor 的生成规则

给定构造器 $c : \Pi x_1 : A_1. \ldots \Pi x_m : A_m.\, I\, a_1 \ldots a_k$，其在 recursor 中的分支类型为：

$$T_c[C] = \Pi x_1 : A_1. \ldots \Pi x_m : A_m. \prod_{h_1 : C\, b_1} \ldots \prod_{h_j : C\, b_j} C\, (c\, x_1 \ldots x_m)$$

其中 $b_1, \ldots, b_j$ 是所有 $A_i$ 中为 $I$-类型的参数（递归出现）。

**Python 实现视角**：

```python
@dataclass
class InductiveDecl:
    name: str
    params: List[Param]      # 参数列表
    indices: List[Expr]      # 索引类型
    level_params: List[str]  # universe 参数
    sort: Level              # 目标 universe
    constructors: List[Constructor]
    recursor: Recursor       # 自动生成的 recursor

@dataclass
class Constructor:
    name: str
    type: Expr               # 构造器的完整类型

@dataclass
class Recursor:
    name: str
    type: Expr               -- 消去子的类型
    num_params: int          -- 参数数量
    num_indices: int         -- 索引数量
    num_motives: int         -- motive 数量（通常为 1）
    num_minors: int          -- 归纳分支数量
    rules: List[RecursorRule]

@dataclass
class RecursorRule:
    ctor: Name               -- 对应的构造器
    nfields: int             -- 构造器字段数
    rhs: Expr                -- 计算规则（ι-reduction 的右边）
```

### 5.7 归纳类型的类型规则

**归纳类型形成**：

$$\frac{\text{well-formed}(\Gamma, \text{inductive } I)}{\Gamma \vdash I : \Pi p_1 : P_1. \ldots \Pi p_n : P_n. \Pi i_1 : A_1. \ldots \Pi i_k : A_k. \text{Sort}\, u} \quad \text{(IND-FORM)}$$

**构造器类型**：

$$\frac{\text{well-formed}(\Gamma, \text{inductive } I)}{\Gamma \vdash c_j : C_j[I]} \quad \text{(CTOR)}$$

**Recursor 类型**：

$$\frac{\text{well-formed}(\Gamma, \text{inductive } I)}{\Gamma \vdash \text{rec}_I : R_I} \quad \text{(REC)}$$

其中 $R_I$ 是上述 recursor 类型。

### 5.8 依赖消除与非依赖消除

Lean 的 recursor 支持**依赖消除**（dependent elimination）：动机（motive）可以依赖于归纳类型的索引。

```lean
-- 非依赖消除：动机不依赖索引
def isZero (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool)
    true                    -- zero 分支
    (fun _ _ => false)      -- succ 分支
    n

-- 依赖消除：动机依赖于索引
def half (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    0                       -- half 0 = 0
    (fun n ih =>            -- half (n+1) = ih + 1 if n even else ih
      Nat.succ (Nat.rec (motive := fun _ => Nat) 0 (fun _ ih2 => Nat.succ ih2) n))
    n
```

---

## 6. 定义环境（Environment）

### 6.1 Environment 的结构

Lean 的 **Environment** 是全局声明的映射，包含所有已定义/已声明的常量：

```
Environment := Name → Option ConstantInfo
```

其中 `ConstantInfo` 包含以下类型：

```lean
inductive ConstantInfo where
  | axiomInfo    : AxiomVal → ConstantInfo
  | defnInfo     : DefinitionVal → ConstantInfo
  | thmInfo      : TheoremVal → ConstantInfo
  | opaqueInfo   : OpaqueVal → ConstantInfo
  | quotInfo     : QuotVal → ConstantInfo
  | inductInfo   : InductiveVal → ConstantInfo
  | ctorInfo     : ConstructorVal → ConstantInfo
  | recInfo      : RecursorVal → ConstantInfo
```

### 6.2 声明（Declaration）的种类

| 声明种类 | Lean 语法 | 核心层表示 | 特性 |
|---------|----------|-----------|------|
| **Axiom** | `axiom foo : A` | `ConstantInfo.axiomInfo` | 无定义体，仅声明类型 |
| **Definition** | `def foo : A := t` | `ConstantInfo.defnInfo` | 可展开的定义，透明 |
| **Theorem** | `theorem foo : A := t` | `ConstantInfo.thmInfo` | 证明，计算时视为不透明（但可展开检查） |
| **Opaque** | `opaque foo : A := t` | `ConstantInfo.opaqueInfo` | 不透明定义，不可展开 |
| **Example** | `example : A := t` | 不加入环境 | 仅用于类型检查，不生成全局常量 |
| **Inductive** | `inductive I ...` | `ConstantInfo.inductInfo` | 归纳类型声明 |
| **Constructor** | 自动生成 | `ConstantInfo.ctorInfo` | 构造器声明 |
| **Recursor** | 自动生成 | `ConstantInfo.recInfo` | 消去子声明 |

**关键区别**：

```lean
-- def: 透明，可在类型检查/证明中展开
def double (n : Nat) : Nat := n + n

-- theorem: 在编译/提取时视为不透明，但在 kernel 检查时可展开
theorem double_zero : double 0 = 0 := rfl

-- opaque: 完全不可展开，仅知道其类型
opaque secret_number : Nat
```

### 6.3 环境的角色

**Environment 作为全局上下文**：

在类型检查/证明检查时，environment 提供全局可用的常量和其类型：

$$\text{Env} \vdash t : A$$

其中 Env 包含所有先前已检查的声明。

**环境扩展规则**：

$$\frac{\text{Env} \text{ well-formed} \quad \text{Env} \vdash t : A \quad \text{name } c \text{ fresh}}
      {\text{Env}, c : A := t \text{ well-formed}} \quad \text{(ENV-EXT-DEF)}$$

### 6.4 局部上下文（Local Context）与全局环境的关系

```
类型检查状态
├── Environment: 全局常量映射
├── LocalContext: 局部假设列表（有序）
│   ├── lctx₁: x₁ : A₁
│   ├── lctx₂: x₂ : A₂
│   └── ...
└── MetavarContext: 元变量/待填证明状态
```

**局部上下文**：

```lean
structure LocalContext where
  decls : Array (Option LocalDecl)  -- 按 de Bruijn 索引排序

inductive LocalDecl where
  | cdecl (index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr)
          (bi : BinderInfo) (kind : LocalDeclKind)  -- 假设/参数
  | ldecl (index : Nat) (fvarId : FVarId) (userName : Name) (type : Expr)
          (value : Expr) (nonDep : Bool) (kind : LocalDeclKind)  -- let 绑定
```

局部上下文使用 **FVarId**（自由变量 ID）表示局部假设，这些在类型检查过程中生成。

### 6.5 Python 实现视角

```python
class Environment:
    """全局环境：Name -> ConstantInfo 的映射"""
    def __init__(self):
        self.constants: Dict[Name, ConstantInfo] = {}
        self.extensions: List[Module] = []  -- 已导入的模块
    
    def add(self, name: Name, info: ConstantInfo) -> 'Environment':
        """扩展环境（函数式更新）"""
        new_env = Environment()
        new_env.constants = dict(self.constants)
        new_env.constants[name] = info
        return new_env
    
    def lookup(self, name: Name) -> Optional[ConstantInfo]:
        return self.constants.get(name)

class LocalContext:
    """局部上下文：有序的局部声明列表"""
    def __init__(self):
        self.decls: List[LocalDecl] = []
    
    def extend(self, decl: LocalDecl) -> 'LocalContext':
        new_ctx = LocalContext()
        new_ctx.decls = self.decls + [decl]
        return new_ctx
    
    def get_type(self, fvar_id: FVarId) -> Optional[Expr]:
        for decl in self.decls:
            if decl.fvar_id == fvar_id:
                return decl.type
        return None
```

---

## 7. 归约机制

Lean 的 kernel 在类型检查过程中执行多种归约。这些归约定义了**定义等价**（definitional equality / conversion）。

### 7.1 β-reduction：函数应用归约

**规则**：$(\lambda x : A.\, t)\, a \triangleright_\beta t[a/x]$

```lean
-- β-归约示例
(λ x : Nat, x + 1) 5  --β-->  5 + 1
```

形式化：

$$\frac{}{(\lambda x : A.\, t)\, a \triangleright_\beta t[a/x]} \quad \text{(BETA)}$$

其中 $t[a/x]$ 是将 $t$ 中的绑定变量 $x$ 替换为 $a$。

**并行/惰性策略**：Lean 使用**弱头范式**（WHNF）策略，只在需要时归约到最外层。

### 7.2 δ-reduction：展开定义

**规则**：全局常量 $c$（定义/定理）被替换为其定义体。

$$\frac{\text{Env}(c) = \text{defnInfo}(A, t)}{c \triangleright_\delta t} \quad \text{(DELTA)}$$

```lean
def double (n : Nat) : Nat := n + n

-- δ-归约示例
double 5  --δ-->  5 + 5
```

**选择性 δ-归约**：

- 对于 `def`：默认可展开
- 对于 `theorem`：在 kernel 中可展开（用于证明检查），在提取时不可展开
- 对于 `opaque`：永不展开

### 7.3 ι-reduction：归纳类型的消去

**规则**：对 recursor 应用于构造器进行计算。

对于归纳类型 $I$ 的构造器 $c_j$ 和 recursor $\text{rec}_I$：

$$\text{rec}_I\, C\, f_1 \ldots f_n \ldots f_n\, (c_j\, a_1 \ldots a_m) \triangleright_\iota f_j\, a_1 \ldots a_m \ldots (\text{rec}_I\, C\, f_1 \ldots f_n \ldots f_n\, a_i) \ldots$$

**Nat.rec 的 ι-归约**：

```lean
Nat.rec C z s zero      --ι-->  z
Nat.rec C z s (succ n)  --ι-->  s n (Nat.rec C z s n)
```

形式化：

$$\frac{}
      {\text{Nat.rec}\, C\, z\, s\, \text{zero} \triangleright_\iota z} \quad \text{(IOTA-ZERO)}$$

$$\frac{}
      {\text{Nat.rec}\, C\, z\, s\, (\text{succ}\, n) \triangleright_\iota s\, n\, (\text{Nat.rec}\, C\, z\, s\, n)} \quad \text{(IOTA-SUCC)}$$

**Bool.rec 的 ι-归约**：

```lean
Bool.rec C f t false  --ι-->  f
Bool.rec C f t true   --ι-->  t
```

### 7.4 ζ-reduction：let 绑定消去

**规则**：$\text{let } x : A := t \text{ in } s \triangleright_\zeta s[t/x]$

```lean
-- ζ-归约示例
let x : Nat := 5 in x + 1  --ζ-->  5 + 1
```

形式化：

$$\frac{}
      {\text{let } x : A := t \text{ in } s \triangleright_\zeta s[t/x]} \quad \text{(ZETA)}$$

### 7.5 弱头范式（WHNF）

**定义**：一个项是 WHNF，如果其最外层不可再归约。

| 形式 | 是否 WHNF | 说明 |
|------|----------|------|
| $\lambda x : A.\, t$ | 是 | λ 抽象已经是范式 |
| $\Pi x : A.\, B$ | 是 | Π 类型已经是范式 |
| $f\, a$（$f$ 是变量） | 是 | 无法进行应用归约 |
| $(\lambda x.\, t)\, a$ | 否 | 可以进行 β-归约 |
| $\text{let } x := t \text{ in } s$ | 否 | 可以进行 ζ-归约 |
| $c$（可展开定义） | 否 | 可以进行 δ-归约 |
| $\text{rec}_I\, \ldots\, (c\, \ldots)$ | 否 | 可以进行 ι-归约 |
| 字面量（如 `Nat.ofNat 42`） | 是 | 已经是 WHNF |

**WHNF 的重要性**：

Lean 的类型检查器只归约到 WHNF，然后进行结构比较。这保证了类型检查的效率。

### 7.6 定义等价（Definitional Equality）

两个项 $t$ 和 $s$ 是**定义等价**的（记作 $t \equiv s$），如果它们通过 β/δ/ι/ζ 归约和 α-转换可以变为相同的项。

$$t \equiv s \iff \exists u.\, t \triangleright^* u \text{ and } s \triangleright^* u \text{ (up to α)}$$

其中 $\triangleright^*$ 表示多步归约。

**类型检查中的使用**：

```python
def is_def_eq(env: Environment, t: Expr, s: Expr) -> bool:
    """检查 t 和 s 是否定义等价"""
    # 快速路径：结构相等
    if alpha_eq(t, s):
        return True
    
    # 将两者归约到 WHNF
    t_whnf = whnf(env, t)
    s_whnf = whnf(env, s)
    
    # 比较 WHNF 的结构
    match (t_whnf, s_whnf):
        case (Lam(_, d1, b1, _), Lam(_, d2, b2, _)):
            return is_def_eq(env, d1, d2) and is_def_eq(env, b1, b2)
        case (ForallE(_, d1, b1, _), ForallE(_, d2, b2, _)):
            return is_def_eq(env, d1, d2) and is_def_eq(env, b1, b2)
        case (App(f1, a1), App(f2, a2)):
            return is_def_eq(env, f1, f2) and is_def_eq(env, a1, a2)
        # ... 其他情况
        case _:
            return False
```


---

## 8. Tactic 系统基础

### 8.1 Tactic 的层次架构

Lean 的 tactic 系统位于核心类型理论之上，提供交互式证明构造的高层接口：

```
用户层（Tactic 语法）
    ↓
Elaborator（Macro/Tactic 展开）
    ↓
Tactic 状态 / Metavariable 求解
    ↓
核心项（Kernel Term）
    ↓
Kernel 类型检查
```

**关键洞察**：Tactic 不直接扩展 Lean 的逻辑力量——它们只是帮助用户构造核心项的**用户界面**。最终的 proof term 仍然通过 kernel 的类型检查。

### 8.2 Elaboration：从 Tactic 到核心项

**Elaboration** 是将表面语法转换为核心项的过程。Tactic elaboration 维护一个**tactic state**：

```lean
structure Tactic.State where
  goals : List MVarId        -- 待证明的目标列表
  mctx : MetavarContext       -- 元变量上下文
  env : Environment           -- 当前环境
```

每个待证明的目标是**一个类型为某命题的元变量**（metavariable）。Tactic 的作用是用一个具体项逐步填充这个元变量。

### 8.3 Metavariable（?m）的机制

**Metavariable** 是待填充的"洞"，表示一个尚未构造的项：

```lean
-- ?m 是一个类型为 A 的元变量
?m : A
```

在核心 AST 中，元变量表示为 `mvar MVarId`。

**元变量上下文**（MetavarContext）跟踪所有未解决的元变量：

```lean
structure MetavarDecl where
  userName       : Name       -- 显示名称
  lctx           : LocalContext  -- 元变量可用的局部假设
  type           : Expr        -- 元变量的类型
  localInstances : LocalInstances  -- 类型类实例缓存
  kind           : MetavarKind  -- Natural / Synthetic / SyntheticOpaque
  numScopeArgs   : Nat         -- 作用域参数数量

structure MetavarContext where
  decls     : PersistentHashMap MVarId MetavarDecl
  lAssignment : PersistentHashMap MVarId Level  -- 层级元变量赋值
  eAssignment : PersistentHashMap MVarId Expr   -- 表达式元变量赋值
  dAssignment : PersistentHashMap MVarId Name   -- 名称延迟赋值
```

**Delayed Abstraction**：

元变量可以携带**延迟抽象**（delayed abstraction），表示其在特定绑定变量下创建：

```
?m[x, y]  -- 元变量 m 在变量 x, y 的抽象下创建
```

这是 Lean 4 的关键创新，使得元变量可以在局部绑定的上下文中正确工作。

### 8.4 Proof State 的结构

**Proof State = Tactic State**，包含：

1. **Goals**：待证明的命题列表，每个是一个元变量
2. **Local Context for each goal**：当前 goal 可用的假设
3. **Metavariable Assignments**：已解决的元变量赋值

```lean
-- 一个典型的 proof state
-- case h₁
-- n : Nat
-- h : n > 0
-- ⊢ n + 1 > 1
```

这里 `n : Nat` 和 `h : n > 0` 在局部上下文中，而 `⊢ n + 1 > 1` 是当前的 goal（元变量）。

### 8.5 基本 Tactic 的原理

#### `intro`：假设引入

**逻辑**：从 $A \to B$ 的目标中引入假设 $A$，将目标变为 $B$。

**实现**：

```
目标：?m : Π x : A. B(x)
intro x  -->  
  创建新局部变量 x : A
  创建新元变量 ?n : B(x)
  赋值 ?m := λ x : A. ?n
  新目标：?n : B(x)
```

```lean
-- 核心项层面
-- 目标: ?m : A → B
-- intro x 后: ?m := λ x : A. ?n,  新目标 ?n : B
```

形式化：

$$\frac{\text{goal} = \text{?m} : \Pi x : A.\, B \quad \text{fresh } x}
      {\text{?m} \mapsto \lambda x : A.\, \text{?n} \quad \text{new goal } \text{?n} : B}$$

#### `apply`：应用定理/函数

**逻辑**：用已有的定理/函数匹配当前目标。

**实现**：

```
目标：?m : B
apply f (其中 f : A₁ → A₂ → ... → Aₙ → B)
  --> 创建元变量 ?m₁ : A₁, ?m₂ : A₂, ..., ?mₙ : Aₙ
  --> 赋值 ?m := f ?m₁ ?m₂ ... ?mₙ
  --> 新目标：?m₁, ?m₂, ..., ?mₙ
```

```lean
example (A B : Prop) (h : A → B) (a : A) : B := by
  apply h      -- 目标变为 A
  exact a      -- 解决 A
```

形式化：

$$\frac{\text{goal} = \text{?m} : B \quad f : \Pi x_1 : A_1. \ldots \Pi x_n : A_n.\, B'}
      {\text{unify}(B, B') \quad \text{?m} \mapsto f\, \text{?m}_1 \ldots \text{?m}_n \quad \text{new goals } \text{?m}_i : A_i}$$

#### `exact`：直接提供证明

**逻辑**：直接用一个项解决当前目标。

```
目标：?m : A
exact t (其中 t : A)
  --> 检查 t : A
  --> 赋值 ?m := t
  --> 无新目标
```

```lean
example (A : Prop) (a : A) : A := by
  exact a
```

#### `rewrite` / `rw`：重写

**逻辑**：用等式替换目标中的子项。

```
目标：?m : P(a)
rw [h] (其中 h : a = b)
  --> 将 P(a) 中的 a 替换为 b
  --> 新目标：?n : P(b)
```

核心机制依赖 **Eq.rec**（等式的 recursor）：

```lean
-- Eq.rec 的类型
Eq.rec : {A : Type u} {a : A} {motive : (x : A) → a = x → Sort v}
  → motive a rfl
  → {b : A} → (h : a = b) → motive b h
```

`rewrite` 实质上是构造一个 `Eq.rec` 的应用：

```lean
-- rw [h : a = b] 在目标 P(a) 上
-- 生成: Eq.rec (motive := fun x (_ : a = x) => P x) (proof_of_P_a) h : P b
```

### 8.6 Tactic 的执行模型

Tactic 在 Lean 4 中是 monadic 的，基于 `TacticM` monad：

```lean
def TacticM := StateRefT Tactic.State MetaM

-- 即: TacticM α = Tactic.State → MetaM (α × Tactic.State)
```

其中 `MetaM` 是元编程 monad，提供元变量创建、赋值、统一化（unification）等功能。

**Tactic 执行流程**：

```
1. 解析 tactic 语法，生成 Syntax 树
2. Elaborator 调用对应的 tactic 函数
3. Tactic 函数操作 Tactic.State（修改 goals, mctx）
4. 当 goals 为空时，proof complete
5. 将所有元变量赋值组合成最终 proof term
6. Kernel 类型检查最终 proof term
```

### 8.7 Unification（统一化）

Tactic 系统的核心是 **unification**——求解使两个项定义等价的元变量赋值。

```
unify(?m t₁ ... tₙ, s)
  -- 尝试找到 ?m 的赋值使其与 s 定义等价
```

Lean 使用 **higher-order pattern unification**（高阶模式统一化），这是一种受限的高阶统一化，保证：

1. 可判定性
2. 最一般解的存在性

### 8.8 Python 实现视角

```python
@dataclass
class TacticState:
    """表示当前 tactic 证明状态"""
    goals: List[MVarId]           -- 待解决的目标（按顺序）
    mctx: MetavarContext          -- 元变量上下文
    env: Environment              -- 全局环境

class TacticM:
    """Tactic Monad: 状态转换 + 可能的失败"""
    def __init__(self, run):
        self.run = run
    
    def bind(self, f):
        return TacticM(lambda state: 
            self.run(state).bind(lambda a, state2: f(a).run(state2)))

# intro tactic 的实现
def tactic_intro(name: str) -> TacticM:
    def run(state: TacticState) -> Result:
        if not state.goals:
            return Result.fail("no goals")
        
        goal_id = state.goals[0]
        goal_decl = state.mctx.get_decl(goal_id)
        goal_type = whnf(state.env, goal_decl.type)
        
        # 检查目标是否是 Π 类型
        match goal_type:
            case Pi(var_name, domain, body, _):
                # 创建新局部变量
                fvar = FVarId.fresh()
                new_lctx = goal_decl.lctx.extend(
                    LocalDecl.cdecl(fvar, name, domain)
                )
                
                # 创建新元变量作为子目标
                new_goal_id = MVarId.fresh()
                new_goal_decl = MetavarDecl(
                    name=name,
                    lctx=new_lctx,
                    type=body,  -- 将 body 中的绑定变量替换为 fvar
                    kind=MetavarKind.Natural
                )
                
                # 赋值原元变量
                proof_term = Lam(name, domain, mvar(new_goal_id))
                new_mctx = state.mctx.assign(goal_id, proof_term)
                new_mctx = new_mctx.add_decl(new_goal_decl)
                
                # 更新状态
                new_state = TacticState(
                    goals=[new_goal_id] + state.goals[1:],
                    mctx=new_mctx,
                    env=state.env
                )
                return Result.ok((), new_state)
            
            case _:
                return Result.fail("goal is not a function type")
    
    return TacticM(run)
```

---

## 9. 形式化规则汇总

### 9.1 语法（抽象语法）

$$\begin{aligned}
t, s, A, B ::=\ & \#n \mid \text{fvar}(id) \mid \text{mvar}(id) \\
& \mid \text{sort}(\ell) \mid \text{const}(c, [\ell_1, \ldots, \ell_k]) \\
& \mid t\, s \mid \lambda x : A.\, t \mid \Pi x : A.\, B \\
& \mid \text{let } x : A := t \text{ in } s \\
& \mid \text{rec}_I([\ell_i], C, f_1, \ldots, f_n, t) \\
\ell ::=\ & 0 \mid 1 \mid \ldots \mid u \mid \ell + 1 \mid \max(\ell_1, \ell_2) \mid \text{imax}(\ell_1, \ell_2) \\
\Gamma ::=\ & \cdot \mid \Gamma, x : A \\
\text{Env} ::=\ & \cdot \mid \text{Env}, c : A := t \mid \text{Env}, c : A 
\end{aligned}$$

### 9.2 上下文形成规则

$$\frac{}{\cdot \text{ well-formed}} \quad \text{(EMPTY-CTX)}$$

$$\frac{\Gamma \text{ well-formed} \quad \Gamma \vdash A : \text{Sort}\, u \quad x \notin \text{dom}(\Gamma)}
      {\Gamma, x : A \text{ well-formed}} \quad \text{(CTX-EXT)}$$

### 9.3 Term Formation（项形成规则）

$$\frac{}{\Gamma, x : A \vdash x : A} \quad \text{(VAR)}$$

$$\frac{(c : A) \in \text{Env}}{\Gamma \vdash c : A} \quad \text{(CONST)}$$

$$\frac{}{\Gamma \vdash \text{Sort}\, \ell : \text{Sort}\, (\ell+1)} \quad \text{(SORT)}$$

$$\frac{\Gamma \vdash A : \text{Sort}\, u \quad \Gamma, x : A \vdash B : \text{Sort}\, v}
      {\Gamma \vdash \Pi x : A.\, B : \text{Sort}\, (\text{imax}\, u\, v)} \quad \text{(PI)}$$

$$\frac{\Gamma, x : A \vdash t : B \quad \Gamma \vdash \Pi x : A.\, B : \text{Sort}\, u}
      {\Gamma \vdash \lambda x : A.\, t : \Pi x : A.\, B} \quad \text{(LAM)}$$

$$\frac{\Gamma \vdash f : \Pi x : A.\, B \quad \Gamma \vdash a : A}
      {\Gamma \vdash f\, a : B[a/x]} \quad \text{(APP)}$$

$$\frac{\Gamma \vdash t : A \quad \Gamma, x : A \vdash s : B \quad \Gamma \vdash B : \text{Sort}\, u}
      {\Gamma \vdash \text{let } x : A := t \text{ in } s : B[t/x]} \quad \text{(LET)}$$

### 9.4 Type Formation（类型形成规则）

类型形成就是项形成中 $A : \text{Sort}\, u$ 的实例。

**归纳类型形成**：

$$\frac{\text{strictly-positive}(\text{constructors}) \quad \text{Env} \vdash \text{parameters} : \text{ok}}
      {\text{Env} \vdash \text{inductive } I\, \bar{p} : \Pi \bar{i} : \bar{A}.\, \text{Sort}\, u : \text{ok}} \quad \text{(IND)}$$

**归纳类型类型**：

$$\frac{(I \text{ inductive in Env})}{\Gamma \vdash I : \Pi \bar{p} : \bar{P}.\, \Pi \bar{i} : \bar{A}.\, \text{Sort}\, u} \quad \text{(IND-TYPE)}$$

**构造器类型**：

$$\frac{(c_j \text{ constructor of } I \text{ in Env})}
      {\Gamma \vdash c_j : \Pi \bar{p} : \bar{P}.\, C_j} \quad \text{(CTOR-TYPE)}$$

**Recursor 类型**：

$$\frac{(\text{rec}_I \text{ in Env})}
      {\Gamma \vdash \text{rec}_I : R_I} \quad \text{(REC-TYPE)}$$

### 9.5 Conversion（转换/定义等价）

$$\frac{\Gamma \vdash t : A \quad \Gamma \vdash B : \text{Sort}\, u \quad A \equiv_\beta B}
      {\Gamma \vdash t : B} \quad \text{(CONV)}$$

**定义等价 $t \equiv s$ 的生成规则**：

**α-等价**：

$$\frac{}{t \equiv t} \quad \text{(REFL)} \qquad
  \frac{t \equiv s}{s \equiv t} \quad \text{(SYM)} \qquad
  \frac{t \equiv u \quad u \equiv s}{t \equiv s} \quad \text{(TRANS)}$$

**β-归约**：

$$\frac{}{(\lambda x : A.\, t)\, a \triangleright_\beta t[a/x]} \quad \text{(BETA)}$$

**δ-归约**：

$$\frac{\text{Env}(c) = \text{defn}(A, t)}{c \triangleright_\delta t} \quad \text{(DELTA)}$$

**ι-归约（一般形式）**：

$$\frac{\text{rec}_I\text{-rule}(c_j, \bar{a}) = r}
      {\text{rec}_I\, C\, \bar{f}\, (c_j\, \bar{a}) \triangleright_\iota r} \quad \text{(IOTA)}$$

**ζ-归约**：

$$\frac{}{\text{let } x := t \text{ in } s \triangleright_\zeta s[t/x]} \quad \text{(ZETA)}$$

**η-扩展**（可选，Lean 在某些情况下使用）：

$$\frac{f : \Pi x : A.\, B}{f \equiv \lambda x : A.\, f\, x} \quad \text{(ETA)}$$

**Congruence**：

$$\frac{t \equiv t' \quad s \equiv s'}{t\, s \equiv t'\, s'} \quad \text{(CONG-APP)}$$

$$\frac{A \equiv A' \quad B \equiv B' \quad t \equiv t'}{\lambda x : A.\, t \equiv \lambda x : A'.\, t'} \quad \text{(CONG-LAM)}$$

$$\frac{A \equiv A' \quad B \equiv B'}{\Pi x : A.\, B \equiv \Pi x : A'.\, B'} \quad \text{(CONG-PI)}$$

### 9.6 Context Extension（上下文扩展）

**环境扩展**：

$$\frac{\text{Env} \text{ wf} \quad \text{Env} \vdash A : \text{Sort}\, u \quad \text{Env} \vdash t : A \quad c \notin \text{Env}}
      {\text{Env}, c : A := t \text{ wf}} \quad \text{(ENV-DEF)}$$

$$\frac{\text{Env} \text{ wf} \quad \text{Env} \vdash A : \text{Sort}\, u \quad c \notin \text{Env}}
      {\text{Env}, c : A \text{ wf}} \quad \text{(ENV-AXIOM)}$$

**归纳声明扩展**：

$$\frac{\text{Env} \text{ wf} \quad \text{inductive-check}(I, \bar{p}, \bar{i}, \bar{c})}
      {\text{Env}, I, \bar{c}, \text{rec}_I \text{ wf}} \quad \text{(ENV-IND)}$$

### 9.7 完整类型检查判断

综合以上规则，Lean 的类型检查可以概括为以下判断：

$$\text{Env} ; \Gamma \vdash t : A$$

读作："在全局环境 Env 和局部上下文 Γ 中，项 t 具有类型 A"。

**核心类型检查算法**（伪代码）：

```
infer(Env, Γ, t):
  match t:
    case #n:
      return lookup_binding(Γ, n)
    case const(c, levels):
      decl = Env.lookup(c)
      return instantiate_universes(decl.type, levels)
    case sort(ℓ):
      return sort(ℓ+1)
    case app(f, a):
      F = infer(Env, Γ, f)
      F_whnf = whnf(Env, F)
      match F_whnf:
        case Π(x:A).B:
          check(Env, Γ, a, A)
          return B[a/x]
        case _: error "function expected"
    case λ(x:A).b:
      check_sort(Env, Γ, A)
      B = infer(Env, Γ, x:A, b)
      return Π(x:A).B
    case Π(x:A).B:
      u = infer_sort(Env, Γ, A)
      v = infer_sort(Env, Γ, x:A, B)
      return sort(imax(u, v))
    case let(x:A := v in b):
      check(Env, Γ, v, A)
      B = infer(Env, Γ, x:A, b)
      return B[v/x]
```

### 9.8 元变量/证明构造判断

Tactic 层扩展了核心判断，增加元变量：

$$\text{Env} ; \Gamma ; \text{Mctx} \vdash t : A$$

其中 Mctx 跟踪未解决的元变量。Tactic 的证明构造通过以下操作：

**元变量创建**：

$$\frac{\Gamma \vdash A : \text{Sort}\, u \quad \text{fresh } \text{?m}}
      {\text{Mctx} \vdash \text{?m} : A \quad \text{pending}} \quad \text{(MVAR-CREATE)}$$

**元变量赋值**：

$$\frac{\text{Mctx} \vdash \text{?m} : A \quad \text{pending} \quad \Gamma \vdash t : A}
      {\text{Mctx}' \vdash \text{?m} := t \quad \text{solved}} \quad \text{(MVAR-ASSIGN)}$$

**统一化**：

$$\frac{\text{Mctx} \vdash t \equiv s \text{ (with mvar assignments)}}
      {\text{Mctx}' \vdash \text{assignments}} \quad \text{(UNIFY)}$$

---

## 附录 A：与 Coq/Agda 的异同

### A.1 与 Coq 的比较

| 特性 | Lean 4 | Coq |
|------|--------|-----|
| 核心演算 | CIC + quotient types | CIC (Predicative/Impredicative variants) |
| Prop impredicativity | 是（仅 Prop） | 可选（Classic/Impredicative Set） |
| Proof Irrelevance | 是（ Prop 内所有证明等价） | 可选（proof irrelevance axiom） |
| 宇宙 | 非累积（名义上）/ 累积约束 | 累积性 |
| Universe Polymorphism | 是 | 是 |
| 归纳类型 | 参数 + 索引 + 递归构造器 | 参数 + 索引 + 递归构造器 |
| Tactic 系统 | `by` 块 + tactic monad | Ltac / Ltac2 / Mtac |
| 元编程 | `MetaM` / `TacticM`（内置） | Ltac / Ltac2 / Elpi |
| 严格正性检查 | 是 | 是 |
| 类型检查性能 | 高度优化（C++ kernel） | 优化（OCaml kernel） |
| 扩展性 | 强（Lean 自身用 Lean 编写） | 强（OCaml 插件） |

### A.2 与 Agda 的比较

| 特性 | Lean 4 | Agda |
|------|--------|------|
| 核心演算 | CIC | MLTT + 归纳定义 + 记录 |
| Prop/Type 分离 | 是（Sort 0 / Sort 1+） | 无（Set 等价于 Lean 的 Type） |
| 终止检查 | 核心层 recursor（结构递归） | 终止检查器（pattern matching） |
| 证明相关性 | Prop 证明无关 | 所有证明相关 |
| 宇宙 | 显式层级 | 显式层级 |
| 类型推断 | 强（约束求解） | 强（unification） |
| 交互式编辑 | VS Code Lean 插件 | Emacs / VS Code Agda mode |
| 归纳记录 | structure = inductive with 1 ctor | record 类型 |

### A.3 核心设计差异

1. **Prop vs. Type**：
   - Lean：显式分离 Prop 和 Type，Prop 内证明无关
   - Agda：无此分离，所有证明可计算
   - Coq：Prop 存在但可选择 proof irrelevance

2. **归纳定义的处理**：
   - Lean/Coq：通过 recursor 消去
   - Agda：通过 pattern matching + 终止检查

3. **Tactic vs. 直接构造**：
   - Lean/Coq：双模式（term mode + tactic mode）
   - Agda：纯 term mode（通过 holes 交互填充）

4. **Universe 系统**：
   - Lean：非累积 + 约束求解（Level 参数显式声明）
   - Coq：累积性 + 自动推断
   - Agda：非累积 + 显式声明

---

## 附录 B：核心数据结构的 Python 实现骨架

以下 Python 代码展示 Lean 4 核心结构的实现框架：

```python
from __future__ import annotations
from dataclasses import dataclass
from typing import List, Dict, Optional, Tuple, Union
from enum import Enum, auto

# ========== 基础标识符 ==========
class Name:
    """分层名称：a.b.c"""
    def __init__(self, parts: List[str]):
        self.parts = parts
    def __str__(self): return ".".join(self.parts)

class FVarId:
    """自由变量唯一 ID"""
    _counter = 0
    @classmethod
    def fresh(cls) -> FVarId:
        cls._counter += 1
        return cls(F"fvar_{cls._counter}")
    def __init__(self, name: str): self.name = name

class MVarId:
    """元变量唯一 ID"""
    _counter = 0
    @classmethod
    def fresh(cls) -> MVarId:
        cls._counter += 1
        return cls(F"mvar_{cls._counter}")
    def __init__(self, name: str): self.name = name

# ========== Universe Level ==========
class Level:
    """Universe 层级表达式"""
    pass

@dataclass
class LZero(Level):  # 0
    pass

@dataclass
class LSucc(Level):  # ℓ + 1
    level: Level

@dataclass
class LMax(Level):  # max(ℓ₁, ℓ₂)
    lhs: Level
    rhs: Level

@dataclass
class LIMAX(Level):  # imax(ℓ₁, ℓ₂)
    lhs: Level
    rhs: Level

@dataclass
class LParam(Level):  # universe 变量
    name: str

def imax(u: Level, v: Level) -> Level:
    """imax(u, v) = 0 if v = 0 else max(u, v)"""
    if isinstance(v, LZero):
        return LZero()
    return LMax(u, v)

# ========== Expr（核心 AST）==========
class Expr:
    """Lean 核心层项的 AST"""
    pass

@dataclass
class BVar(Expr):  # 绑定变量（de Bruijn 索引）
    idx: int

@dataclass
class FVar(Expr):  # 自由变量（局部常量）
    id: FVarId

@dataclass
class MVar(Expr):  # 元变量
    id: MVarId

@dataclass
class Sort(Expr):  # Universe
    level: Level

@dataclass
class Const(Expr):  # 全局常量
    name: Name
    levels: List[Level]  -- universe 实例化参数

@dataclass
class App(Expr):  # 应用
    fn: Expr
    arg: Expr

@dataclass
class Lam(Expr):  # λ 抽象
    name: str
    domain: Expr
    body: Expr
    binder_info: BinderInfo

@dataclass
class ForallE(Expr):  # Π 类型
    name: str
    domain: Expr
    body: Expr
    binder_info: BinderInfo

@dataclass
class LetE(Expr):  # let 绑定
    name: str
    type: Expr
    value: Expr
    body: Expr

class BinderInfo(Enum):
    DEFAULT = auto()
    IMPLICIT = auto()
    STRICT_IMPLICIT = auto()
    INST_IMPLICIT = auto()  -- 类型类实例隐式参数

# ========== 局部声明 ==========
@dataclass
class LocalDecl:
    fvar_id: FVarId
    user_name: str
    type: Expr
    # let 绑定有 value，cdecl 没有
    value: Optional[Expr] = None

# ========== 元变量声明 ==========
@dataclass
class MetavarDecl:
    user_name: str
    lctx: LocalContext
    type: Expr
    kind: MetavarKind

class MetavarKind(Enum):
    NATURAL = auto()
    SYNTHETIC = auto()
    SYNTHETIC_OPAQUE = auto()

# ========== 局部上下文 ==========
class LocalContext:
    def __init__(self):
        self.decls: List[LocalDecl] = []
    
    def extend(self, decl: LocalDecl) -> LocalContext:
        new_ctx = LocalContext()
        new_ctx.decls = self.decls + [decl]
        return new_ctx
    
    def lookup(self, fvar_id: FVarId) -> Optional[LocalDecl]:
        for d in self.decls:
            if d.fvar_id == fvar_id:
                return d
        return None

# ========== 元变量上下文 ==========
class MetavarContext:
    def __init__(self):
        self.decls: Dict[MVarId, MetavarDecl] = {}
        self.assignments: Dict[MVarId, Expr] = {}
    
    def add_decl(self, decl: MetavarDecl) -> MetavarContext:
        new_mctx = MetavarContext()
        new_mctx.decls = dict(self.decls)
        new_mctx.assignments = dict(self.assignments)
        # ... 添加 decl
        return new_mctx
    
    def assign(self, mvar_id: MVarId, value: Expr) -> MetavarContext:
        new_mctx = MetavarContext()
        new_mctx.decls = dict(self.decls)
        new_mctx.assignments = dict(self.assignments)
        new_mctx.assignments[mvar_id] = value
        return new_mctx
    
    def get_assigned(self, mvar_id: MVarId) -> Optional[Expr]:
        return self.assignments.get(mvar_id)

# ========== 常量信息 ==========
class ConstantInfo:
    pass

@dataclass
class AxiomVal(ConstantInfo):
    name: Name
    type: Expr
    level_params: List[str]

@dataclass
class DefinitionVal(ConstantInfo):
    name: Name
    type: Expr
    value: Expr
    level_params: List[str]

@dataclass
class TheoremVal(ConstantInfo):
    name: Name
    type: Expr
    value: Expr
    level_params: List[str]

@dataclass
class InductiveVal(ConstantInfo):
    name: Name
    type: Expr
    level_params: List[str]
    num_params: int
    num_indices: int
    all: List[Name]  -- 相互归纳组中的所有类型
    constructors: List[Name]

@dataclass
class RecursorVal(ConstantInfo):
    name: Name
    type: Expr
    level_params: List[str]
    num_params: int
    num_indices: int
    num_motives: int
    num_minors: int
    rules: List[RecursorRule]

@dataclass
class RecursorRule:
    ctor: Name
    nfields: int
    rhs: Expr

# ========== 环境 ==========
class Environment:
    def __init__(self):
        self.constants: Dict[Name, ConstantInfo] = {}
    
    def add(self, name: Name, info: ConstantInfo) -> Environment:
        new_env = Environment()
        new_env.constants = dict(self.constants)
        new_env.constants[name] = info
        return new_env
    
    def lookup(self, name: Name) -> Optional[ConstantInfo]:
        return self.constants.get(name)

# ========== 归约 ==========
def whnf(env: Environment, e: Expr) -> Expr:
    """Weak Head Normal Form：归约到最外层不可归约"""
    while True:
        match e:
            case App(Lam(_, _, body, _), arg):
                # β-归约
                e = substitute(body, arg)
            case LetE(_, _, value, body, _):
                # ζ-归约
                e = substitute(body, value)
            case MVar(id) if (assigned := mctx.get_assigned(id)):
                e = assigned
            case Const(name, _) if (decl := env.lookup(name)):
                match decl:
                    case DefinitionVal(_, _, value, _):
                        e = instantiate_universes(value, decl)
                    case _:
                        return e
            case App(fn, _) if is_recursor_app(env, e):
                if reduced := try_iota_reduce(env, e):
                    e = reduced
                else:
                    return e
            case _:
                return e

def is_def_eq(env: Environment, t: Expr, s: Expr, mctx: MetavarContext) -> bool:
    """检查 t 和 s 是否定义等价"""
    # 快速路径
    if alpha_eq(t, s):
        return True
    
    # WHNF 比较
    t_whnf = whnf(env, t)
    s_whnf = whnf(env, s)
    
    # 结构递归比较
    match (t_whnf, s_whnf):
        case (Lam(_, d1, b1, _), Lam(_, d2, b2, _)):
            return is_def_eq(env, d1, d2, mctx) and is_def_eq(env, b1, b2, mctx)
        case (ForallE(_, d1, b1, _), ForallE(_, d2, b2, _)):
            return is_def_eq(env, d1, d2, mctx) and is_def_eq(env, b1, b2, mctx)
        case (App(f1, a1), App(f2, a2)):
            return is_def_eq(env, f1, f2, mctx) and is_def_eq(env, a1, a2, mctx)
        case _:
            return False

# ========== 类型检查 ==========
def infer_type(env: Environment, lctx: LocalContext, e: Expr, 
               mctx: MetavarContext) -> Tuple[Expr, MetavarContext]:
    """推断 e 的类型"""
    match e:
        case BVar(idx):
            decl = lctx.decls[idx]  # de Bruijn 索引查找
            return (decl.type, mctx)
        case FVar(id):
            decl = lctx.lookup(id)
            return (decl.type, mctx)
        case MVar(id):
            decl = mctx.decls[id]
            return (decl.type, mctx)
        case Sort(level):
            return (Sort(LSucc(level)), mctx)
        case Const(name, levels):
            decl = env.lookup(name)
            return (instantiate_universes(decl.type, levels), mctx)
        case Lam(name, domain, body, _):
            # 检查 domain 的类型
            u, mctx = infer_sort(env, lctx, domain, mctx)
            # 扩展上下文
            new_lctx = lctx.extend(LocalDecl(FVarId.fresh(), name, domain))
            B, mctx = infer_type(env, new_lctx, body, mctx)
            return (ForallE(name, domain, abstract_local(B, 0), BinderInfo.DEFAULT), mctx)
        case ForallE(name, domain, body, _):
            u, mctx = infer_sort(env, lctx, domain, mctx)
            new_lctx = lctx.extend(LocalDecl(FVarId.fresh(), name, domain))
            v, mctx = infer_sort(env, new_lctx, body, mctx)
            return (Sort(imax(u, v)), mctx)
        case App(fn, arg):
            F, mctx = infer_type(env, lctx, fn, mctx)
            F_whnf = whnf(env, F)
            match F_whnf:
                case ForallE(_, domain, body, _):
                    A, mctx = infer_type(env, lctx, arg, mctx)
                    if not is_def_eq(env, A, domain, mctx):
                        raise TypeError("type mismatch")
                    return (substitute(body, arg), mctx)
                case _:
                    raise TypeError("function expected")
        # ... 其他情况
```

---

## 总结

Lean 4 的核心逻辑结构建立于**带类型的 λ 演算 + 依赖类型 + 归纳构造演算**之上，通过 Curry-Howard 同构将逻辑命题与类型统一。其关键设计特点包括：

1. **证明无关的 Prop**：使得逻辑层和计算层清晰分离
2. **严格的归纳类型**：通过 positivity 条件保证一致性
3. **多重归约策略**：β/δ/ι/ζ 共同定义定义等价
4. **Universe 多态**：支持通用的、层级无关的编程
5. **Tactic → 核心项**：所有交互式证明最终归约为类型检查

本报告提供的形式化规则和数据结构可直接用于指导一个 Lean-like 类型检查器的 Python 实现。

---

*报告完成。所有核心概念均附有形式化定义，适合直接用于实现参考。*
