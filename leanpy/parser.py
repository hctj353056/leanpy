"""
LeanPy 解析器：递归下降解析器，解析类 Lean 语法。

设计说明：
- 使用递归下降方法，手写解析器
- 处理左递归（函数应用）通过循环而非递归
- 使用 de Bruijn 索引表示局部变量
- 支持分层名称（如 Nat.add）

支持的语法：
  expr     ::= lambda | forall | let | arrow | app
  lambda   ::= "fun" binders "=>" expr
  forall   ::= "forall" binders "," expr | "Π" binders "," expr
  let      ::= "let" name ":" expr ":=" expr ";" expr
  arrow    ::= pi_expr ("->" pi_expr)*      （右结合）
  pi_expr  ::= atom+
  atom     ::= ident | "(" expr ")" | "Sort" level | "Type" | "Prop" | nat_lit
  binders  ::= binder+
  binder   ::= "(" name+ ":" expr ")"
  ident    ::= [a-zA-Z_][a-zA-Z0-9_]* ("." [a-zA-Z_][a-zA-Z0-9_]*)*
  level    ::= nat | ident | "(" "max" level level ")"
  nat_lit  ::= [0-9]+

优先级（从高到低）：
  1. 原子（标识符、括号、字面量、Sort/Type/Prop）
  2. 函数应用（左结合）
  3. 箭头类型（右结合）
  4. lambda / forall / let
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Optional, List, Tuple, Dict

from .name import Name, mk_name
from .level import Level
from .expr import Expr, BinderInfo
from .environment import Environment


# ===== 词法标记 =====

class TokenKind:
    """词法标记类型"""
    IDENT = "IDENT"       # 标识符
    NAT = "NAT"           # 自然数
    LPAREN = "LPAREN"     # (
    RPAREN = "RPAREN"     # )
    COLON = "COLON"       # :
    ARROW = "ARROW"       # ->
    DARROW = "DARROW"     # =>
    COMMA = "COMMA"       # ,
    DOT = "DOT"           # .
    SEMICOLON = "SEMICOLON"  # ;
    ASSIGN = "ASSIGN"     # :=
    FUN = "FUN"           # fun
    FORALL = "FORALL"     # forall / Π
    LET = "LET"           # let
    SORT = "SORT"         # Sort
    TYPE = "TYPE"         # Type
    PROP = "PROP"         # Prop
    EOF = "EOF"           # 文件结束


@dataclass
class Token:
    """词法标记"""
    kind: str
    text: str
    pos: int


# ===== 词法分析器（Lexer） =====

class Lexer:
    """将输入字符串转换为词法标记序列"""
    
    # 关键字映射
    KEYWORDS: Dict[str, str] = {
        'fun': TokenKind.FUN,
        'forall': TokenKind.FORALL,
        'Π': TokenKind.FORALL,
        'Pi': TokenKind.FORALL,
        'let': TokenKind.LET,
        'Sort': TokenKind.SORT,
        'Type': TokenKind.TYPE,
        'Prop': TokenKind.PROP,
    }
    
    def __init__(self, text: str):
        self.text = text
        self.pos = 0
        self.length = len(text)
    
    def next_token(self) -> Token:
        """获取下一个词法标记"""
        self._skip_whitespace()
        
        if self.pos >= self.length:
            return Token(TokenKind.EOF, "", self.pos)
        
        start = self.pos
        ch = self.text[self.pos]
        
        # 括号
        if ch == '(':
            self.pos += 1
            return Token(TokenKind.LPAREN, "(", start)
        if ch == ')':
            self.pos += 1
            return Token(TokenKind.RPAREN, ")", start)
        
        # 冒号
        if ch == ':':
            self.pos += 1
            # 检查 :=
            if self.pos < self.length and self.text[self.pos] == '=':
                self.pos += 1
                return Token(TokenKind.ASSIGN, ":=", start)
            return Token(TokenKind.COLON, ":", start)
        
        # 箭头 ->
        if ch == '-':
            self.pos += 1
            if self.pos < self.length and self.text[self.pos] == '>':
                self.pos += 1
                return Token(TokenKind.ARROW, "->", start)
            # 不是 ->，可能是标识符的一部分（如负数？）
            self.pos -= 1  # 回退
        
        # 胖箭头 =>
        if ch == '=':
            self.pos += 1
            if self.pos < self.length and self.text[self.pos] == '>':
                self.pos += 1
                return Token(TokenKind.DARROW, "=>", start)
            # 单独的 = 不是有效标记，但先当 IDENT 处理
            return Token(TokenKind.IDENT, "=", start)
        
        # 逗号
        if ch == ',':
            self.pos += 1
            return Token(TokenKind.COMMA, ",", start)
        
        # 分号
        if ch == ';':
            self.pos += 1
            return Token(TokenKind.SEMICOLON, ";", start)
        
        # 点（用于分层名称）
        if ch == '.':
            self.pos += 1
            return Token(TokenKind.DOT, ".", start)
        
        # 自然数
        if ch.isdigit():
            return self._read_nat(start)
        
        # 标识符（含 Unicode 字母支持）
        if ch.isalpha() or ch == '_':
            return self._read_ident(start)
        
        # 未知字符，跳过
        self.pos += 1
        return self.next_token()
    
    def tokenize(self) -> List[Token]:
        """将所有输入转为标记列表"""
        tokens = []
        while True:
            tok = self.next_token()
            tokens.append(tok)
            if tok.kind == TokenKind.EOF:
                break
        return tokens
    
    def _skip_whitespace(self):
        """跳过空白字符和注释"""
        while self.pos < self.length:
            ch = self.text[self.pos]
            if ch.isspace():
                self.pos += 1
            # 跳过行注释 --
            elif ch == '-' and self.pos + 1 < self.length and self.text[self.pos + 1] == '-':
                while self.pos < self.length and self.text[self.pos] != '\n':
                    self.pos += 1
            # 跳过块注释 /-
            elif ch == '/' and self.pos + 1 < self.length and self.text[self.pos + 1] == '-':
                self.pos += 2
                depth = 1
                while self.pos < self.length and depth > 0:
                    if self.text[self.pos] == '/' and self.pos + 1 < self.length and self.text[self.pos + 1] == '-':
                        depth += 1
                        self.pos += 2
                    elif self.text[self.pos] == '-' and self.pos + 1 < self.length and self.text[self.pos + 1] == '/':
                        depth -= 1
                        self.pos += 2
                    else:
                        self.pos += 1
            else:
                break
    
    def _read_nat(self, start: int) -> Token:
        """读取自然数"""
        while self.pos < self.length and self.text[self.pos].isdigit():
            self.pos += 1
        return Token(TokenKind.NAT, self.text[start:self.pos], start)
    
    def _read_ident(self, start: int) -> Token:
        """读取标识符"""
        while (self.pos < self.length and 
               (self.text[self.pos].isalnum() or self.text[self.pos] == '_')):
            self.pos += 1
        text = self.text[start:self.pos]
        kind = self.KEYWORDS.get(text, TokenKind.IDENT)
        return Token(kind, text, start)


# ===== 解析器 =====

class ParserError(Exception):
    """解析错误"""
    pass


class Parser:
    """递归下降解析器，将类 Lean 语法字符串解析为 Expr AST。
    
    核心设计：
    - 使用 de Bruijn 索引管理局部变量
    - local_names 列表：索引 0 = 最近绑定的变量
    - 函数应用使用循环实现左结合
    - 箭头类型使用递归实现右结合
    
    示例解析过程：
    "fun (x : A) => x" 
    → 进入 parse_lambda
    → 绑定 x : A，local_names = ["x", ...]
    → 解析 body "x"，查找 local_names 得到索引 0
    → 构造 Expr.lam("x", A, Expr.bvar(0))
    """
    
    def __init__(self, text: str, env: Optional[Environment] = None):
        self.text = text
        self.env = env or Environment()
        # 词法分析
        self.lexer = Lexer(text)
        self.tokens = self.lexer.tokenize()
        self.token_pos = 0
        # 局部变量名称到 de Bruijn 索引的映射
        # 索引 0 = 最近绑定的变量（最内层）
        self.local_names: List[str] = []
    
    # ===== 词法工具 =====
    
    @property
    def current(self) -> Token:
        """当前标记"""
        if self.token_pos < len(self.tokens):
            return self.tokens[self.token_pos]
        return self.tokens[-1]  # EOF
    
    def peek(self, offset: int = 0) -> Token:
        """查看向前 offset 个标记"""
        pos = self.token_pos + offset
        if pos < len(self.tokens):
            return self.tokens[pos]
        return self.tokens[-1]
    
    def advance(self) -> Token:
        """消耗当前标记并前进"""
        tok = self.current
        if self.token_pos < len(self.tokens) - 1:
            self.token_pos += 1
        return tok
    
    def expect(self, kind: str) -> Token:
        """期望特定类型的标记"""
        tok = self.current
        if tok.kind != kind:
            raise ParserError(
                f"Expected {kind}, got {tok.kind} ({tok.text}) at position {tok.pos}")
        return self.advance()
    
    def match(self, kind: str) -> bool:
        """检查当前标记是否匹配"""
        return self.current.kind == kind
    
    def match_text(self, text: str) -> bool:
        """检查当前标记的文本"""
        return self.current.text == text
    
    def consume_if(self, kind: str) -> bool:
        """如果是期望类型则消耗"""
        if self.match(kind):
            self.advance()
            return True
        return False
    
    # ===== 错误报告 =====
    
    def error(self, msg: str) -> ParserError:
        """创建解析错误"""
        tok = self.current
        context = self.text[max(0, tok.pos-10):tok.pos+20]
        return ParserError(f"{msg} at position {tok.pos} near '{context}'")
    
    # ===== 核心解析方法 =====
    
    def parse_expr(self) -> Expr:
        """解析顶层表达式。
        
        根据当前标记选择正确的解析方法。
        """
        tok = self.current
        
        if tok.kind == TokenKind.FUN:
            return self.parse_lambda()
        elif tok.kind == TokenKind.FORALL:
            return self.parse_forall()
        elif tok.kind == TokenKind.LET:
            return self.parse_let()
        else:
            return self.parse_arrow()
    
    def parse_lambda(self) -> Expr:
        """解析 λ/fun 表达式：fun (x : A) (y : B) => body
        
        处理多绑定器，构建嵌套的 λ。
        例如：fun (x : A) (y : B) => body 
        → λ x : A. λ y : B. body
        """
        self.expect(TokenKind.FUN)  # 消耗 fun
        
        # 解析绑定器列表
        binders = self.parse_binders()
        
        self.expect(TokenKind.DARROW)  # 消耗 =>
        
        # 解析 body
        body = self.parse_expr()
        
        # 构建嵌套的 λ（从内到外）
        # 需要反向处理绑定器，因为最外层的 λ 对应最近绑定
        for name, dtype in reversed(binders):
            # 移除绑定的名称
            self._pop_local(name)
            body = Expr.lam(name, dtype, body)
        
        return body
    
    def parse_forall(self) -> Expr:
        """解析 forall/Π 表达式：forall (A : Type) (x : A), B
        
        也处理非依赖箭头 A -> B。
        """
        self.expect(TokenKind.FORALL)  # 消耗 forall/Π
        
        # 解析绑定器列表
        binders = self.parse_binders()
        
        self.expect(TokenKind.COMMA)  # 消耗 ,
        
        # 解析 body
        body = self.parse_expr()
        
        # 构建嵌套的 Π
        for name, dtype in reversed(binders):
            self._pop_local(name)
            body = Expr.forallE(name, dtype, body)
        
        return body
    
    def parse_let(self) -> Expr:
        """解析 let 表达式：let x : A := v; body
        
        注意：let 绑定会引入新的局部变量。
        """
        self.expect(TokenKind.LET)  # 消耗 let
        
        # 变量名
        name_tok = self.expect(TokenKind.IDENT)
        name = name_tok.text
        
        self.expect(TokenKind.COLON)
        
        # 类型
        dtype = self.parse_expr()
        
        self.expect(TokenKind.ASSIGN)  # 消耗 :=
        
        # 值
        value = self.parse_expr()
        
        self.expect(TokenKind.SEMICOLON)  # 消耗 ;
        
        # 在 body 的作用域中，name 是可见的
        # 但 let 不会用 de Bruijn 索引直接表示
        # Lean 的 letE 构造会处理这个
        body = self.parse_expr()
        
        # 清理局部变量
        self._remove_local(name)
        
        return Expr.letE(name, dtype, value, body)
    
    def parse_arrow(self) -> Expr:
        """解析箭头类型（右结合）：A -> B -> C = A -> (B -> C)
        
        箭头类型是非依赖函数类型的语法糖：
        A -> B = Π _ : A. B
        """
        left = self.parse_app()
        
        if self.match(TokenKind.ARROW):
            # 右结合：收集所有部分然后反向构建
            parts = [left]
            while self.consume_if(TokenKind.ARROW):
                parts.append(self.parse_app())
            
            # 从右向左构建：A -> B -> C = A -> (B -> C)
            result = parts[-1]
            for src in reversed(parts[:-1]):
                result = Expr.mk_arrow(src, result)
            return result
        
        return left
    
    def parse_app(self) -> Expr:
        """解析函数应用（左结合）：f a b = ((f a) b)
        
        使用循环而非递归来处理左结合的函数应用链。
        """
        atoms = []
        
        # 至少解析一个原子
        atoms.append(self.parse_pi_expr())
        
        # 连续解析原子直到不能再解析
        while self._can_start_atom(self.current):
            atoms.append(self.parse_pi_expr())
        
        # 左结合：(((f a1) a2) a3)
        if len(atoms) == 1:
            return atoms[0]
        
        result = atoms[0]
        for arg in atoms[1:]:
            result = Expr.app(result, arg)
        
        return result
    
    def parse_pi_expr(self) -> Expr:
        """解析 pi 级别的表达式（原子序列中的单个原子）"""
        return self.parse_atom()
    
    def parse_atom(self) -> Expr:
        """解析原子表达式。
        
        原子包括：
        - 标识符（局部变量或全局常量）
        - 括号表达式
        - Sort/Type/Prop
        - 自然数字面量
        """
        tok = self.current
        
        match tok.kind:
            case TokenKind.IDENT:
                return self.parse_ident_or_atom()
            
            case TokenKind.NAT:
                return self.parse_nat_lit()
            
            case TokenKind.LPAREN:
                self.advance()  # 消耗 (
                expr = self.parse_expr()
                self.expect(TokenKind.RPAREN)
                return expr
            
            case TokenKind.SORT:
                return self.parse_sort_expr()
            
            case TokenKind.TYPE:
                self.advance()
                return Expr.Type
            
            case TokenKind.PROP:
                self.advance()
                return Expr.Prop
            
            case _:
                raise self.error(f"Unexpected token: {tok.text} (kind={tok.kind})")
    
    def parse_sort_expr(self) -> Expr:
        """解析 Sort 表达式：Sort, Sort 0, Sort 1, ..."""
        self.expect(TokenKind.SORT)  # 消耗 Sort
        
        # 检查是否有层级参数
        if self.match(TokenKind.NAT):
            level_num = int(self.advance().text)
            return Expr.sort(level_of_nat(level_num))
        
        # 没有参数就是 Sort 0（Prop）
        return Expr.sort(Level.zero())
    
    def parse_ident_or_atom(self) -> Expr:
        """解析标识符，可能是局部变量或全局常量。"""
        tok = self.advance()  # 消耗标识符
        name_parts = [tok.text]
        
        # 处理分层名称：Nat.add
        while self.match(TokenKind.DOT):
            self.advance()  # 消耗 .
            next_tok = self.expect(TokenKind.IDENT)
            name_parts.append(next_tok.text)
        
        name_str = ".".join(name_parts)
        
        # 先检查是否是局部变量
        for i, local_name in enumerate(self.local_names):
            if local_name == name_str:
                # 局部变量使用 de Bruijn 索引
                # local_names[0] 是最内层绑定，对应索引 0
                return Expr.bvar(i)
        
        # 否则是全局常量
        name = self._name_from_parts(name_parts)
        return Expr.const(name)
    
    def parse_ident(self) -> Name:
        """解析标识符为 Name 对象。"""
        tok = self.advance()
        name_parts = [tok.text]
        
        while self.match(TokenKind.DOT):
            self.advance()
            next_tok = self.expect(TokenKind.IDENT)
            name_parts.append(next_tok.text)
        
        return self._name_from_parts(name_parts)
    
    def parse_nat_lit(self) -> Expr:
        """解析自然数字面量。"""
        tok = self.advance()
        val = int(tok.text)
        return Expr.lit_nat(val)
    
    def parse_binders(self) -> List[Tuple[str, Expr]]:
        """解析绑定器列表：((x : A) (y : B) ...)
        
        返回 [(name, type), ...] 的列表。
        同时将新绑定的名称加入 local_names。
        """
        binders = []
        
        while self.match(TokenKind.LPAREN):
            self.advance()  # 消耗 (
            
            # 名称列表（支持多名称同类型：
            names = []
            name_tok = self.expect(TokenKind.IDENT)
            names.append(name_tok.text)
            
            while self.match(TokenKind.IDENT):
                names.append(self.advance().text)
            
            self.expect(TokenKind.COLON)
            
            # 类型
            dtype = self.parse_expr()
            
            self.expect(TokenKind.RPAREN)
            
            # 为每个名称创建绑定
            for name in names:
                self.local_names.insert(0, name)  # 最内层在索引 0
                binders.append((name, dtype))
        
        return binders
    
    # ===== 辅助方法 =====
    
    def _can_start_atom(self, tok: Token) -> bool:
        """检查标记是否可以开始一个原子表达式。"""
        return tok.kind in (
            TokenKind.IDENT, TokenKind.NAT, 
            TokenKind.LPAREN, TokenKind.SORT,
            TokenKind.TYPE, TokenKind.PROP
        )
    
    def _name_from_parts(self, parts: List[str]) -> Name:
        """从部分列表创建 Name"""
        return mk_name(*parts)
    
    def _pop_local(self, name: str):
        """从 local_names 中移除一个名称。"""
        if self.local_names and self.local_names[0] == name:
            self.local_names.pop(0)
    
    def _remove_local(self, name: str):
        """从 local_names 中移除指定名称的所有出现。"""
        self.local_names = [n for n in self.local_names if n != name]


# ===== 便捷函数 =====

def parse_expr(text: str, env: Optional[Environment] = None) -> Expr:
    """解析表达式字符串，返回 Expr AST。
    
    示例：
        >>> parse_expr("fun (x : Nat) => x")
        (λ x : Nat. #0)
        
        >>> parse_expr("Nat -> Bool")
        (Nat → ...)
        
        >>> parse_expr("forall (A : Type), A -> A")
        (Π A : Type. (A → ...))
    """
    parser = Parser(text, env)
    return parser.parse_expr()


def parse_decl(text: str) -> Tuple[str, Expr, Optional[Expr]]:
    """解析声明：name : type := value?
    
    示例：
        >>> parse_decl("id : forall (A : Type), A -> A := fun (A : Type) (x : A) => x")
        ('id', Π A : Type. (A → ...), λ A : Type. λ x : A. #0)
    """
    parser = Parser(text)
    
    # 名称
    name_tok = parser.expect(TokenKind.IDENT)
    name = name_tok.text
    
    parser.expect(TokenKind.COLON)
    
    # 类型
    dtype = parser.parse_expr()
    
    # 可选的定义
    value = None
    if parser.consume_if(TokenKind.ASSIGN):
        value = parser.parse_expr()
    
    return (name, dtype, value)


# ===== 层级解析辅助 =====

def level_of_nat(n: int) -> Level:
    """从自然数创建层级"""
    result = Level.zero()
    for _ in range(n):
        result = Level.succ(result)
    return result
