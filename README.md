# LeanPy

> 用 Python 与 Lean 定理证明器交互的工具库

## 项目概述

LeanPy 是一个实验性项目，旨在探索 Lean 4 与 Python 的交互方式，提供形式化证明能力。

**核心目标：**
- 在 Python 中实现 Lean 核心类型系统
- 提供简洁的定理证明接口
- 支持形式化数学推理

## 快速开始

```python
import leanpy

# 创建表达式
expr = leanpy.Expr("∀ n : Nat, n + 0 = n")

# 类型检查
result = leanpy.type_check(expr)
print(result)
```

## 项目结构

```
leanpy/
├── leanpy/              # 核心代码
│   ├── __init__.py      # 模块入口
│   ├── environment.py   # 环境管理
│   ├── expr.py          # 表达式表示
│   ├── inductive.py     # 归纳类型
│   ├── level.py         # 宇宙层级
│   ├── name.py          # 名称管理
│   ├── parser.py        # 解析器
│   ├── reducer.py       # 归约器
│   ├── tactic.py        # 策略系统
│   ├── typechecker.py   # 类型检查器
│   ├── examples.py      # 示例代码
│   └── test_core.py     # 核心测试
├── LEAN_EXPLAINED.md    # Lean 概念解释
├── lean_core_structure.md # Lean 核心结构文档
├── README.md            # 项目说明
└── LICENSE              # 许可证
```

## 核心模块

| 模块 | 说明 |
|------|------|
| `environment.py` | Lean 环境管理，维护定义和定理 |
| `expr.py` | 表达式的数据结构和操作 |
| `inductive.py` | 归纳类型定义和处理 |
| `level.py` | 宇宙层级系统 |
| `name.py` | 名称和命名空间管理 |
| `parser.py` | 表达式解析 |
| `reducer.py` | β-归约和 δ-归约 |
| `tactic.py` | 证明策略 |
| `typechecker.py` | 类型检查和推断 |

## 安装

```bash
# 克隆仓库
git clone https://github.com/hctj353056/leanpy.git
cd leanpy

# 安装依赖
pip install -e .

# 可选：安装 Lean 4 (via elan)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

## 依赖

- Python >= 3.10
- Lean 4 (via elan) - 可选

## 版本历史

| 版本 | 日期 | 变更内容 |
|------|------|----------|
| v1.0 | - | 初始版本，实现核心类型系统 |

## 作者

蜉蝣子 ♡

## 许可证

MIT License

---

*蜉熵阁 · LeanPy项目*
