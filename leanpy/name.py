"""
Lean 风格的分层名称系统。

Lean 使用 Name 来表示标识符，支持层次化命名（如 `Nat.add`）。
这与 Python 的模块化命名空间类似。
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Union, Optional


@dataclass(frozen=True)
class Name:
    """
    Lean 风格的分层名称。
    
    Name 可以是：
    - Anonymous: 匿名名称
    - Str: 字符串前缀 + 字符串组件
    - Num: 字符串前缀 + 数字组件（用于内部生成的名称）
    
    例如：`Nat.add` 表示为 Name(Str(Name.Anonymous, "Nat"), "add")
    """
    
    class Anonymous:
        """匿名名称（根）"""
        def __repr__(self): return "<anonymous>"
    
    ANONYMOUS = Anonymous()
    
    prefix: Union[Name, Name.Anonymous]
    component: Union[str, int]
    
    def __init__(self, prefix=None, component=None):
        if prefix is None and component is None:
            object.__setattr__(self, 'prefix', Name.ANONYMOUS)
            object.__setattr__(self, 'component', "")
        elif isinstance(prefix, (str, int)) and component is None:
            # Name("foo") -> Name(Anonymous, "foo")
            object.__setattr__(self, 'prefix', Name.ANONYMOUS)
            object.__setattr__(self, 'component', prefix)
        else:
            object.__setattr__(self, 'prefix', prefix if prefix is not None else Name.ANONYMOUS)
            object.__setattr__(self, 'component', component if component is not None else "")
    
    @staticmethod
    def anonymous() -> Name:
        """创建匿名名称"""
        return Name(Name.ANONYMOUS, "")
    
    @staticmethod
    def str_name(prefix, s: str) -> Name:
        """创建字符串组件名称"""
        return Name(prefix, s)
    
    @staticmethod
    def num_name(prefix, n: int) -> Name:
        """创建数字组件名称（内部使用）"""
        return Name(prefix, n)
    
    def is_anonymous(self) -> bool:
        return isinstance(self.prefix, Name.Anonymous) and self.component == ""
    
    def __str__(self) -> str:
        if self.is_anonymous():
            return "_"
        parts = []
        current = self
        while not isinstance(current, Name.Anonymous) and not current.is_anonymous():
            if isinstance(current.component, str) and current.component:
                parts.append(current.component)
            elif isinstance(current.component, int):
                parts.append(f"_{current.component}")
            current = current.prefix
        return ".".join(reversed(parts))
    
    def __repr__(self) -> str:
        return f"Name({str(self)})"
    
    def __hash__(self) -> int:
        return hash((id(self.prefix) if isinstance(self.prefix, Name.Anonymous) else hash(self.prefix), 
                     self.component))
    
    def __eq__(self, other) -> bool:
        if not isinstance(other, Name):
            return False
        if self.is_anonymous() and other.is_anonymous():
            return True
        return self.prefix == other.prefix and self.component == other.component
    
    def append(self, suffix: str) -> Name:
        """追加字符串组件"""
        return Name(self, suffix)
    
    def append_num(self, n: int) -> Name:
        """追加数字组件"""
        return Name(self, n)


# 便捷函数
def mk_name(*parts: str) -> Name:
    """从多个部分创建名称，如 mk_name("Nat", "add") -> Nat.add"""
    result = Name(Name.ANONYMOUS, parts[0])
    for p in parts[1:]:
        result = result.append(p)
    return result
