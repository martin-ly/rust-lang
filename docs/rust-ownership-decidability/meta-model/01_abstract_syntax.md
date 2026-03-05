# Rust 所有权系统元模型 - 抽象语法

## 1. 元元语言说明

本文档使用以下元语言：

- `::=` 表示语法产生式
- `|` 表示或
- `[...]` 表示可选
- `{...}` 表示重复零次或多次
- `(...)` 表示分组
- **粗体** 表示终结符
- *斜体* 表示元变量

## 2. 词法元素

### 2.1 标识符

```bnf
identifier ::= letter (letter | digit | '_')*
letter     ::= 'a' | ... | 'z' | 'A' | ... | 'Z'
digit      ::= '0' | ... | '9'
```

### 2.2 关键字

```text
let, mut, ref, box, fn, struct, enum, match, if, else, loop, break, continue, return, trait, impl, where, for, while, unsafe, const, static, type, as, move, Self, self
```

## 3. 类型语法

### 3.1 基础类型

```bnf
τ ::=                         (* 类型 *)
  | B                         (* 基础类型 *)
  | &ρ ω τ                    (* 引用类型 *)
  | Box τ                     (* 唯一指针 *)
  | (τ₁, ..., τₙ)             (* 元组类型 *)
  | struct_name<τ₁, ..., τₙ>  (* 结构体类型 *)
  | enum_name<τ₁, ..., τₙ>    (* 枚举类型 *)
  | trait_name<τ₁, ..., τₙ>   (* trait 对象 *)
  | ρ                         (* 区域/生命周期 *)

B ::= () | bool | i8 | i16 | i32 | i64 | i128 | isize | u8 | u16 | u32 | u64 | u128 | usize | char | str

ω ::= uniq | shrd             (* 可变性: 唯一或共享 *)
```

### 3.2 区域 (Lifetime/Region)

```bnf
ρ ::=                         (* 区域 *)
  | 'static                   (* 静态生命周期 *)
  | 'r                        (* 命名生命周期 *)
  | ρ ∪ ρ                     (* 区域并集 *)

*r ::=                        (* 区域变量 *)
  | r₁ | r₂ | ...             (* 无限可枚举集合 *)
```

## 4. 表达式语法

### 4.1 核心表达式

```bnf
e ::=                         (* 表达式 *)
  | v                         (* 值 *)
  | x                         (* 变量 *)
  | *p                        (* 解引用 *)
  | &ρ ω p                    (* 借用 *)
  | box e                     (* 装箱 *)
  | (e₁, ..., eₙ)             (* 元组构造 *)
  | e; e                      (* 序列 *)
  | let ω x : τ = e; e        (* 变量绑定 *)
  | p = e                     (* 赋值 *)
  | fn_name::<τ₁, ..., τₙ>(e₁, ..., eₙ)  (* 函数调用 *)
  | match e { arm₁, ..., armₙ }          (* 匹配 *)
  | if e { e } else { e }                (* 条件 *)
  | loop { e }                           (* 循环 *)
  | break [e]                            (* 跳出 *)
  | continue                             (* 继续 *)
  | return e                             (* 返回 *)
  | abort!                               (* 中止 *)

arm ::= pattern => e          (* 匹配分支 *)

pattern ::=
  | _                         (* 通配 *)
  | x                         (* 变量绑定 *)
  | v                         (* 字面量 *)
  | (pattern₁, ..., patternₙ) (* 元组解构 *)
  | constructor(pattern₁, ..., patternₙ) (* 枚举解构 *)
```

### 4.2 位置表达式 (Place Expressions)

```bnf
p ::=                         (* 位置 *)
  | x                         (* 变量 *)
  | *p                        (* 解引用 *)
  | p.n                       (* 字段投影 *)
  | p[e]                      (* 索引 *)
  | p[e₁..e₂]                 (* 切片 *)
```

### 4.3 值

```bnf
v ::=
  | ()                        (* 单元 *)
  | true | false              (* 布尔 *)
  | n                         (* 整数 *)
  | c                         (* 字符 *)
  | "string"                  (* 字符串 *)
  | ℓ                         (* 内存位置 *)
  | (v₁, ..., vₙ)             (* 元组值 *)
  | closure                   (* 闭包 *)
```

## 5. 声明语法

### 5.1 函数

```bnf
fn_decl ::=
  | fn fn_name<r₁, ..., rₙ>(x₁: τ₁, ..., xₘ: τₘ) -> τ where { constraints } { e }

constraints ::=
  | r₁: r₂                    (* 区域包含关系 *)
  | trait_bound               (* trait 约束 *)
```

### 5.2 结构体

```bnf
struct_decl ::=
  | struct struct_name<r₁, ..., rₙ> { field₁: τ₁, ..., fieldₘ: τₘ }
```

### 5.3 枚举

```bnf
enum_decl ::=
  | enum enum_name<r₁, ..., rₙ> { variant₁, ..., variantₘ }

variant ::=
  | constructor_name          (* 无数据变体 *)
  | constructor_name(τ₁, ..., τₙ)  (* 元组变体 *)
  | constructor_name { field₁: τ₁, ..., fieldₙ: τₙ } (* 结构体变体 *)
```

### 5.4 Trait

```bnf
trait_decl ::=
  | trait trait_name<r₁, ..., rₙ> for τ where { constraints } {
      method_sig₁;
      ...
      method_sigₘ;
    }

method_sig ::=
  | fn method_name(x₁: τ₁, ..., xₙ: τₙ) -> τ

impl_decl ::=
  | impl trait_name<r₁, ..., rₙ> for τ where { constraints } {
      method_impl₁
      ...
      method_implₘ
    }
```

## 6. 程序

```bnf
program ::=
  | { decl }* e_main         (* 一系列声明和主表达式 *)
```

## 7. 语法范畴总结

| 符号 | 含义 | 英文 |
|------|------|------|
| τ | 类型 | Type |
| ρ | 区域/生命周期 | Region/Lifetime |
| ω | 可变性 | Mutability |
| e | 表达式 | Expression |
| p | 位置表达式 | Place expression |
| v | 值 | Value |
| x | 变量 | Variable |
| r | 区域变量 | Region variable |
| ℓ | 内存位置 | Location |

## 8. 语法 sugar

### 8.1 可变性简化

```
&τ    ≡ & _ shrd τ    (* 不可变引用 *)
&mut τ ≡ & _ uniq τ   (* 可变引用 *)
```

### 8.2 生命周期省略

```
&τ    ≡ &'anon τ      (* 匿名生命周期 *)
```

## 9. 示例程序

### 9.1 简单借用

```rust
let mut x: i32 = 5;
let y: &i32 = &x;
*x  // 使用
```

### 9.2 可变借用

```rust
let mut x: i32 = 5;
let y: &mut i32 = &mut x;
*y = 10;
x  // 错误: x 被借用
```

### 9.3 函数定义

```rust
fn swap<'a>(x: &'a mut i32, y: &'a mut i32) {
    let tmp = *x;
    *x = *y;
    *y = tmp;
}
```

---

**状态**: 草案 v0.1
**最后更新**: 2026-03-05
