> **EN**: Macro FAQ
> **Summary**: Authoritative concept page for `04 Faq`. Content migrated from `crates/c11_macro_system_proc/docs/tier_01_foundations/04_faq.md`.
> **受众**: [进阶]
> **内容分级**: [参考级]
> **Bloom 层级**: 分析 → 评价
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A+P** — Application + Procedure
> **双维定位**: A×Eva — 评估宏（Macro）使用场景与限制
> **前置依赖**: [过程宏（Procedural Macro）](07_proc_macro.md) · [宏术语表](32_macro_glossary.md)
> **后置概念**: [宏（Macro）卫生性](35_macro_hygiene.md) · [生产级宏开发](31_production_grade_macro_development.md)
> **定理链**: Common Question ⟹ Mechanism Explanation ⟹ Best Practice
>
> **权威来源**: 本页为 `Macro FAQ` 的权威概念页；crate 文档仅保留导航 stub。

# 常见问题 (FAQ) - C11 Macro System

**最后更新**: 2025-12-11

本文档汇总了 Rust 宏系统中的常见问题和解答。

---

## 📋 目录

- [常见问题 (FAQ) - C11 Macro System](#常见问题-faq---c11-macro-system)
  - [📋 目录](#-目录)
  - [🎨 宏基础问题](#-宏基础问题)
    - [Q1: 声明宏 vs. 过程宏，何时使用哪个？](#q1-声明宏-vs-过程宏何时使用哪个)
    - [Q2: 宏与函数的区别是什么？](#q2-宏与函数的区别是什么)
    - [Q3: 宏会影响性能吗？](#q3-宏会影响性能吗)
  - [🔧 声明宏问题](#-声明宏问题)
    - [Q4: 如何调试声明宏？](#q4-如何调试声明宏)
    - [Q5: 声明宏的卫生性如何工作？](#q5-声明宏的卫生性如何工作)
    - [Q6: 如何处理宏的多个分支？](#q6-如何处理宏的多个分支)
  - [⚙️ 过程宏问题](#️-过程宏问题)
    - [Q7: 如何开始写第一个过程宏？](#q7-如何开始写第一个过程宏)
    - [Q8: syn 和 quote 是必须的吗？](#q8-syn-和-quote-是必须的吗)
    - [Q9: 如何测试过程宏？](#q9-如何测试过程宏)
    - [Q10: 过程宏可以读取文件吗？](#q10-过程宏可以读取文件吗)
  - [🛠️ 工程实践问题](#️-工程实践问题)
    - [Q11: 如何组织宏项目结构？](#q11-如何组织宏项目结构)
    - [Q12: 宏的错误消息如何优化？](#q12-宏的错误消息如何优化)
    - [Q13: 如何发布宏库？](#q13-如何发布宏库)
  - [🐛 故障排查问题](#-故障排查问题)
    - [Q14: "recursion limit reached" 错误如何解决？](#q14-recursion-limit-reached-错误如何解决)
    - [Q15: "cannot find macro" 错误如何解决？](#q15-cannot-find-macro-错误如何解决)
    - [Q16: 为什么宏展开后有编译错误？](#q16-为什么宏展开后有编译错误)
  - [💡 高级话题](#-高级话题)
    - [Q17: 如何构建 DSL？](#q17-如何构建-dsl)
    - [Q18: 宏可以生成宏吗？](#q18-宏可以生成宏吗)
    - [Q19: 如何实现零成本抽象？](#q19-如何实现零成本抽象)
  - [认知路径](#认知路径)
  - [定理链](#定理链)
  - [反命题](#反命题)
  - [反向推理](#反向推理)
  - [过渡段](#过渡段)

---

## 🎨 宏基础问题

### Q1: 声明宏 vs. 过程宏，何时使用哪个？

**声明宏（Declarative Macro）** (`macro_rules!`) 适用于：

- 简单的代码模式
- 快速原型
- 不需要复杂解析

```rust
macro_rules! vec_of_strings {
    ($($element:expr),*) => {
        vec![$(String::from($element)),*]
    };
}
```

**过程宏** 适用于：

- 复杂的代码生成
- Derive 实现
- 需要精确控制

```rust
#[derive(MyTrait)]
struct MyStruct { }
```

**建议**: 优先尝试声明宏，复杂需求再用过程宏。

---

### Q2: 宏与函数的区别是什么？

| 特性     | 宏                 | 函数       |
| :--- | :--- | :--- |
| 执行时机 | 编译时             | 运行时（Runtime）     |
| 输入     | TokenStream/语法树 | 值         |
| 输出     | 代码               | 值         |
| 类型检查 | 展开后             | 调用时     |
| 性能     | 零成本             | 有调用开销 |
| 调试     | 困难               | 容易       |

**示例**:

```rust
// 宏：编译时展开
macro_rules! five {
    () => { 5 };
}
let x = five!(); // 展开为 let x = 5;

// 函数：运行时调用
fn five() -> i32 { 5 }
let x = five(); // 运行时调用函数
```

---

### Q3: 宏会影响性能吗？

**编译时**: 会增加编译时间

- 宏展开需要时间
- 复杂宏影响更大

**运行时（Runtime）**: 零性能开销

- 宏完全展开为代码
- 与手写代码相同

```rust
// 宏版本
let v = vec![1, 2, 3];

// 手写等价代码
let mut temp_vec = Vec::new();
temp_vec.push(1);
temp_vec.push(2);
temp_vec.push(3);
let v = temp_vec;

// 性能完全相同！
```

**建议**: 合理使用宏，避免过度嵌套。

---

## 🔧 声明宏问题

### Q4: 如何调试声明宏？

**方法 1**: 使用 `cargo expand`

```bash
cargo install cargo-expand
cargo expand my_module
```

**方法 2**: 使用 `dbg!` 和 `stringify!`

```rust
macro_rules! debug_macro {
    ($($tt:tt)*) => {
        {
            println!("Expanded: {}", stringify!($($tt)*));
            $($tt)*
        }
    };
}
```

**方法 3**: 逐步简化

```rust
// 1. 先用简单输入测试
my_macro!(x);

// 2. 逐步增加复杂度
my_macro!(x, y);
my_macro!(x, y, z);
```

---

### Q5: 声明宏的卫生性如何工作？

**卫生性规则**:

1. 宏内定义的变量不泄露到外部
2. 宏外的变量在宏内可见（如果显式引用（Reference））

```rust
macro_rules! using_a {
    ($e:expr) => {
        {
            let a = 42; // 局部变量，不影响外部
            $e
        }
    }
}

let a = 13;
let result = using_a!(a + a); // 26，使用外部 a
println!("a = {}", a); // 13，外部 a 未变
```

**打破卫生性** (不推荐):

```rust
macro_rules! break_hygiene {
    () => {
        let __internal_var = 42; // 可能冲突
    };
}
```

---

### Q6: 如何处理宏的多个分支？

使用模式匹配（Pattern Matching）的多个分支：

```rust
macro_rules! calculate {
    // 加法
    ($a:expr + $b:expr) => {
        $a + $b
    };

    // 乘法
    ($a:expr * $b:expr) => {
        $a * $b
    };

    // 单个值
    ($e:expr) => {
        $e
    };
}

let x = calculate!(2 + 3);  // 5
let y = calculate!(2 * 3);  // 6
let z = calculate!(42);     // 42
```

**注意**: 更具体的模式放在前面。

---

## ⚙️ 过程宏问题

### Q7: 如何开始写第一个过程宏？

**步骤 1**: 创建库项目

```bash
cargo new my_macro --lib
```

**步骤 2**: 配置 `Cargo.toml`

```toml
[lib]
proc-macro = true

[dependencies]
syn = { version = "2.0", features = ["full"] }
quote = "1.0"
proc-macro2 = "1.0"
```

**步骤 3**: 编写宏

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(HelloMacro)]
pub fn hello_macro_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let expanded = quote! {
        impl HelloMacro for #name {
            fn hello_macro() {
                println!("Hello, Macro! My name is {}!", stringify!(#name));
            }
        }
    };

    TokenStream::from(expanded)
}
```

---

### Q8: syn 和 quote 是必须的吗？

**不是必须**，但强烈推荐：

**不使用 syn/quote** (困难):

```rust
#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // 手动解析 TokenStream，非常繁琐
    let tokens: Vec<_> = input.into_iter().collect();
    // ... 复杂的解析逻辑
}
```

**使用 syn/quote** (简单):

```rust
#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let expanded = quote! { /* 代码 */ };
    TokenStream::from(expanded)
}
```

**建议**: 除非特殊需求，否则使用 syn/quote。

---

### Q9: 如何测试过程宏？

**方法 1**: 集成测试

```rust
// tests/integration.rs
use my_macro::MyMacro;

#[derive(MyMacro)]
struct TestStruct;

#[test]
fn test_macro() {
    // 验证宏生成的代码
}
```

**方法 2**: trybuild (测试编译错误)

```rust
#[test]
fn ui_tests() {
    let t = trybuild::TestCases::new();
    t.pass("tests/ui/pass/*.rs");
    t.compile_fail("tests/ui/fail/*.rs");
}
```

**方法 3**: macrotest (快照测试)

```rust
#[test]
fn test_macro_expansion() {
    macrotest::expand("tests/expand/*.rs");
}
```

---

### Q10: 过程宏可以读取文件吗？

**可以，但需谨慎**:

```rust
use std::fs;

#[proc_macro]
pub fn include_config(_item: TokenStream) -> TokenStream {
    let config = fs::read_to_string("config.toml")
        .expect("Failed to read config");

    // 处理配置...
}
```

**注意事项**:

1. **路径问题**: 使用 `CARGO_MANIFEST_DIR` 环境变量
2. **缓存问题**: cargo 可能不会重新编译
3. **可移植性**: 文件可能不存在

**更好的方案**: 使用 `include_str!` 或 build script。

---

## 🛠️ 工程实践问题

### Q11: 如何组织宏项目结构？

**推荐结构**:

```text
my_project/
├── Cargo.toml
├── my_macro/           # 宏库
│   ├── Cargo.toml      # proc-macro = true
│   └── src/
│       └── lib.rs
├── my_macro_derive/    # Derive 宏
│   ├── Cargo.toml
│   └── src/
│       └── lib.rs
└── src/                # 主库
    └── lib.rs          # 重导出宏
```

**主库重导出**:

```rust
// src/lib.rs
pub use my_macro_derive::MyDerive;

// 用户只需
use my_project::MyDerive;
```

---

### Q12: 宏的错误消息如何优化？

**技巧 1**: 使用 `compile_error!`

```rust
macro_rules! only_two_args {
    ($a:expr, $b:expr) => { /* OK */ };
    ($($args:tt)*) => {
        compile_error!("This macro accepts exactly 2 arguments")
    };
}
```

**技巧 2**: 使用 Span

```rust
use syn::spanned::Spanned;

let span = field.span();
return syn::Error::new(span, "Field must be public")
    .to_compile_error()
    .into();
```

**技巧 3**: 提供建议

```rust
return syn::Error::new(
    span,
    "Missing #[id] attribute. Try: #[derive(MyTrait)] #[id(1)]"
).to_compile_error().into();
```

---

### Q13: 如何发布宏库？

**步骤 1**: 完善文档

````rust
//! # My Macro
//!
//! This macro does...
//!
//! ## Example
//!
//! ```
//! use my_macro::MyMacro;
//!
//! #[derive(MyMacro)]
//! struct Example;
//! ```

#[proc_macro_derive(MyMacro)]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // ...
}
````

**步骤 2**: 添加测试

```rust
// tests/integration.rs
#[test]
fn test_basic() { /* ... */ }

#[test]
fn test_edge_cases() { /* ... */ }
```

**步骤 3**: 发布

```bash
cargo publish --dry-run
cargo publish
```

**建议**:

- 提供丰富示例
- 清晰的错误消息
- 完整的 CI/CD

---

## 🐛 故障排查问题

### Q14: "recursion limit reached" 错误如何解决？

**原因**: 宏递归展开次数超过限制（默认128）。

**解决方案 1**: 增加递归限制

```rust
#![recursion_limit = "256"]
```

**解决方案 2**: 重构宏，减少递归

```rust
// ❌ 不好：深度递归
macro_rules! recursive {
    () => { 0 };
    ($x:tt $($rest:tt)*) => {
        1 + recursive!($($rest)*)
    };
}

// ✅ 好：迭代
macro_rules! count {
    ($($x:tt)*) => {
        <[()]>::len(&[$(replace_expr!($x ())),*])
    };
}
```

---

### Q15: "cannot find macro" 错误如何解决？

**原因**: 宏未正确导入或定义。

**解决方案 1**: 确认宏已导出

```rust
// 库中
#[macro_export]
macro_rules! my_macro {
    // ...
}
```

**解决方案 2**: 正确导入

```rust
// 使用方
use my_crate::my_macro;

// 或
#[macro_use]
extern crate my_crate;
```

**解决方案 3**: 检查 Cargo.toml

```toml
[dependencies]
my_crate = "1.0"
```

---

### Q16: 为什么宏展开后有编译错误？

**调试步骤**:

1. **查看展开结果**

   ```bash
   cargo expand
   ```

2. **检查生成的代码**

   ```rust
   // 确保生成的代码是有效的 Rust 代码
   ```

3. **验证作用域**

   ```rust
   // 确保使用的类型/trait 在作用域内
   use std::fmt::Display; // 如果生成的代码需要
   ```

4. **检查卫生性问题**

   ```rust
   // 使用完整路径
   ::std::vec::Vec::new()
   ```

---

## 💡 高级话题

### Q17: 如何构建 DSL？

**步骤 1**: 设计语法

```rust
// 目标语法
html! {
    <div class="container">
        <h1>"Hello"</h1>
    </div>
}
```

**步骤 2**: 定义函数式宏

```rust
#[proc_macro]
pub fn html(input: TokenStream) -> TokenStream {
    // 解析自定义语法
    // 生成 Rust 代码
}
```

**步骤 3**: 自定义解析器

```rust
struct HtmlParser {
    input: ParseStream,
}

impl HtmlParser {
    fn parse_element(&mut self) -> Element {
        // 解析 <tag>...</tag>
    }
}
```

---

### Q18: 宏可以生成宏吗？

**可以，但有限制**:

```rust
macro_rules! make_macro {
    ($name:ident) => {
        macro_rules! $name {
            () => { println!("Hello from {}!", stringify!($name)); };
        }
    };
}

make_macro!(greet);
greet!(); // Hello from greet!
```

**限制**:

- 只能在同一作用域
- 不能跨 crate 导出

---

### Q19: 如何实现零成本抽象？

**原则**: 宏展开的代码应与手写代码相同。

**验证方法 1**: cargo expand

```bash
cargo expand my_module
```

**验证方法 2**: LLVM IR 比较

```bash
cargo rustc --release -- --emit llvm-ir
```

**验证方法 3**: 基准测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_macro(c: &mut Criterion) {
    c.bench_function("with_macro", |b| {
        b.iter(|| my_macro!(black_box(data)))
    });

    c.bench_function("hand_written", |b| {
        b.iter(|| hand_written(black_box(data)))
    });
}
```

**示例**: vec! 宏的零成本

```rust
// 宏
let v = vec![1, 2, 3];

// 手写
let mut temp = Vec::new();
temp.push(1);
temp.push(2);
temp.push(3);
let v = temp;

// 生成完全相同的机器码！
```

---

**上一步**: [术语表](/crates/c11_macro_system_proc/docs/tier_01_foundations/03_glossary.md)
**下一步**: [进入 Tier 2 实践层](/crates/c11_macro_system_proc/docs/tier_02_guides/README.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

> **向下引用（Reference）**: 参见 [17_macro_patterns](../../02_intermediate/06_macros_and_metaprogramming/17_macro_patterns.md)

## 认知路径

1. **问题识别**: 识别宏初学者与使用者在实际开发中反复遇到的典型问题。
2. **概念建立**: 掌握声明宏与过程宏的选型、调试、测试与限制等常见问题的答案。
3. **机制推理**: 通过问题 ⟹ 机制解释 ⟹ 最佳实践的定理链深化理解。
4. **边界辨析**: 辨析“宏只是代码替换”等反命题，理解卫生性、span 与类型系统（Type System）约束。
5. **迁移应用**: 将 FAQ 与卫生性、生产级开发主题链接。

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| 问题驱动 ⟹ 针对性学习 | 按真实困惑组织内容 | 读者能快速找到当前痛点 |
| 机制解释 ⟹ 避免死记硬背 | 说明宏展开、卫生性、span 等底层原理 | 用户能举一反三解决新问题 |
| 最佳实践 ⟹ 减少反模式 | 给出可执行的代码示例与工具推荐 | FAQ 直接转化为工程规范 |

## 反命题

> **反命题 1**: "宏只是简单的代码替换" ⟹ 不成立。Rust 宏受卫生性、span 与类型系统（Type System）约束，行为远比文本替换复杂。
>
> **反命题 2**: "过程宏一定比声明宏好" ⟹ 不成立。简单模式匹配（Pattern Matching）场景下声明宏更轻量。
>
> **反命题 3**: "FAQ 不需要示例" ⟹ 不成立。可运行的最小示例是验证答案正确性的关键。
>
## 反向推理

> **反向推理 1**: 团队反复询问同一宏行为 ⟸ 说明 FAQ 未覆盖该场景或答案缺少示例。
>
> **反向推理 2**: 线上出现宏卫生性相关 bug ⟸ 说明开发者对 hygiene/span 的理解不足，应补充 FAQ 解释。
>
## 过渡段

> **过渡**: 从常见问题过渡到机制解释，可以理解“为什么”比“怎么做”更能避免重复踩坑。
>
> **过渡**: 从机制解释过渡到最佳实践，可以建立从知识到工程规范的转化路径。
>
> **过渡**: 从最佳实践过渡到生产级开发，可以将 FAQ 融入团队宏开发流程。
>
