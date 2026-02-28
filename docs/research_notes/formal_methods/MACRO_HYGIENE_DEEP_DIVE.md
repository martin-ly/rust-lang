# 宏卫生性 (Macro Hygiene) 深度解析

> **文档状态**: ✅ 完整
> **理论级别**: L2 - 形式化数学
> **适用范围**: `macro_rules!` 和过程宏

---

## 1. 卫生性机制概述

### 什么是宏卫生性？

**卫生性 (Hygiene)** 确保宏生成的标识符不会与宏外部的标识符意外冲突。

```rust
// 定义宏
macro_rules! using_a {
    ($e:expr) => {
        let a = 42;
        $e
    };
}

// 使用宏
let four = using_a!(a / 10);  // ❌ 编译错误！
// error: cannot find value `a` in this scope
```

尽管宏内部定义了 `a`，但宏外部的 `a / 10` 无法访问它 —— 这就是卫生性保护。

---

## 2. 语法上下文 (Syntax Context)

### Def CTX-1（语法上下文定义）

每个标识符携带**语法上下文** (Syntax Context)，用于区分不同作用域的同名标识符：

$$
\text{Identifier} ::= \text{name}: \text{String} \times \text{context}: \text{ContextId}
$$

```
┌─────────────────────────────────────────┐
│           语法上下文架构                 │
├─────────────────────────────────────────┤
│  源代码层                               │
│  let a = 1;  // context: #1             │
│                                         │
│  宏定义层                               │
│  macro! { let a = 2; }  // context: #2  │
│                                         │
│  宏调用层                               │
│  macro! { a }  // context: #3           │
└─────────────────────────────────────────┘
```

### 上下文层级

| 层级 | 描述 | 示例 |
|------|------|------|
| #0 | 根上下文 | 顶层代码 |
| #1 | 宏定义上下文 | `macro_rules!` 内部 |
| #2 | 宏调用上下文 | 调用宏的位置 |
| #3+ | 嵌套宏上下文 | 宏展开中的宏 |

---

## 3. 标识符分类

### Def ID-CLASS（标识符分类）

标识符按用途分为三类：

$$
\text{IdClass} ::= \text{Binding} \mid \text{Reference} \mid \text{Label}
$$

| 类型 | 示例 | 说明 |
|------|------|------|
| Binding | `let x`, `fn foo` | 创建新绑定 |
| Reference | `x + 1` | 引用已有绑定 |
| Label | `'label: loop` | 控制流标签 |

### 绑定标识符的卫生性

```rust
macro_rules! make_var {
    ($name:ident, $value:expr) => {
        let $name = $value;  // 在宏定义上下文创建绑定
    };
}

make_var!(x, 42);

// x 在这里不可见！因为绑定在宏定义上下文
// println!("{}", x);  // ❌ 编译错误
```

### 引用标识符的解析

```rust
macro_rules! use_var {
    ($e:expr) => {
        $e + a  // 'a' 引用在宏定义上下文解析
    };
}

let a = 10;
let result = use_var!(5);  // 引用宏调用上下文的 'a'
// 结果: 15
```

---

## 4. 卫生性规则形式化

### Rule HYGIENE-1（绑定隔离规则）

宏内部创建的绑定标识符，只在宏定义上下文可见：

$$
\frac{\text{macro\_def} \vdash \text{let } x = e}{\text{macro\_call} \not\vdash x}
$$

### Rule HYGIENE-2（引用解析规则）

宏内部的引用标识符，优先在宏定义上下文解析，其次是宏调用上下文：

$$
\frac{\Gamma_{\text{def}} \vdash x: \tau}{\Gamma_{\text{call}} \not\vdash x \Rightarrow \text{使用 } \Gamma_{\text{def}}(x)}
$$

### Rule HYGIENE-3（混合上下文规则）

通过 `$var` 传入的标识符，在调用上下文解析：

```rust
macro_rules! mixed_context {
    ($var:ident) => {
        // $var 在调用上下文解析
        let $var = 42;  // 但创建的绑定仍在宏定义上下文
    };
}

mixed_context!(y);
// y 仍然不可见（绑定在宏定义上下文）
```

---

## 5. 跨 Crate 卫生性

### Def CROSS-CRATE（跨 Crate 卫生性）

宏导出的标识符需要在不同 crate 间保持卫生性：

```rust
// crate_a: 定义宏
#[macro_export]
macro_rules! export_var {
    () => {
        let secret = 42;  // 在 crate_a 上下文中
    };
}

// crate_b: 使用宏
use crate_a::export_var;

fn main() {
    export_var!();
    // secret 不可见（卫生性保持）
}
```

### $crate 变量

```rust
#[macro_export]
macro_rules! use_internal {
    () => {
        // $crate 确保正确引用宏定义 crate 的内部项
        $crate::internal_function()
    };
}
```

| 变量 | 含义 | 使用场景 |
|------|------|----------|
| `$crate` | 宏定义的 crate | 访问宏所在 crate 的私有项 |

---

## 6. 非卫生性操作

某些宏操作**故意不卫生**，用于元编程：

| 宏 | 卫生性 | 用途 |
|----|--------|------|
| `stringify!` | ❌ 非卫生 | 将标识符转为字符串 |
| `concat!` | ❌ 非卫生 | 字符串拼接 |
| `include!` | ❌ 非卫生 | 包含外部文件 |
| `module_path!` | ❌ 非卫生 | 获取模块路径 |

```rust
let x = 42;
macro_rules! check_hygiene {
    () => {
        // stringify! 非卫生：直接处理标记
        println!("{}", stringify!(x));  // 输出 "x"
    };
}
```

---

## 7. 实战：打破卫生性（谨慎使用）

### 使用 `#[macro_export]` + 组合

```rust
// 组合多个宏来"传递"标识符
macro_rules! define_and_use {
    ($name:ident, $value:expr, $body:expr) => {{
        let $name = $value;
        $body
    }};
}

let result = define_and_use!(x, 42, x * 2);
// result = 84
// 注意：x 仍然只在块内可见
```

### 使用 const 泛型传递（高级技巧）

```rust
macro_rules! const_hygiene_break {
    ($name:ident) => {
        {
            struct $name;
            impl $name {
                const VALUE: i32 = 42;
            }
            $name::VALUE
        }
    };
}

let val = const_hygiene_break!(MyConst);
```

---

## 8. 过程宏的卫生性

过程宏使用 `Span` 系统实现卫生性：

```rust
use proc_macro::{Span, TokenStream, TokenTree, Ident};

#[proc_macro]
pub fn hygienic_macro(input: TokenStream) -> TokenStream {
    // 使用调用点的 Span
    let call_site = Span::call_site();

    // 使用宏定义点的 Span（混合策略）
    let mixed_site = Span::mixed_site();

    // 创建带特定上下文的标识符
    let new_ident = Ident::new("generated_var", mixed_site);

    // ...
}
```

| Span 类型 | 行为 |
|-----------|------|
| `call_site()` | 宏调用上下文 |
| `mixed_site()` | 混合上下文（Rust 1.45+） |
| `def_site()` | 宏定义上下文（不稳定） |

---

## 9. 总结

| 概念 | 关键点 |
|------|--------|
| 语法上下文 | 每个标识符携带上下文 ID |
| 绑定隔离 | 宏内绑定不泄漏到外部 |
| 引用解析 | 优先宏定义上下文 |
| 跨 Crate | `$crate` 变量确保正确引用 |
| 非卫生操作 | `stringify!`, `concat!` 等 |

---

**最后更新**: 2026-02-28
**参考**: [Rust Reference - Macros Hygiene](https://doc.rust-lang.org/reference/macros-by-example.html#hygiene)
