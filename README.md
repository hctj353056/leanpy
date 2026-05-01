# LeanPy

> 用 Python 与 Lean 定理证明器交互的工具库

## 简介

LeanPy 是一个实验性项目，旨在探索 Lean 4 与 Python 的交互方式。

## 安装

```bash
# 克隆仓库
git clone https://github.com/hctj353056/leanpy.git
cd leanpy

# 安装依赖
pip install -e .

# 或使用 elan 安装 Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

## 快速开始

```python
import leanpy

# 连接 Lean 服务器
server = leanpy.Server()

# 发送证明请求
result = server.prove("∀ n : Nat, n + 0 = n")
print(result)
```

## 项目结构

```
leanpy/
├── leanpy/           # 核心代码
│   ├── __init__.py
│   ├── server.py     # Lean 服务器交互
│   └── prove.py      # 证明辅助
├── examples/         # 示例代码
├── tests/            # 测试
└── README.md
```

## 依赖

- Python >= 3.10
- Lean 4 (via elan)

## 许可证

MIT
