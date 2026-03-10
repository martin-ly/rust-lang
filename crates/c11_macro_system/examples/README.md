# C11 宏系统 - 示例中心

> **创建日期**: 2025-10-22
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 100% 完成
> **概念说明**: 本示例集展示 Rust 宏编程的各种技术，包括声明宏 (macro_rules!)、过程宏（派生宏、属性宏、函数宏）以及高级宏技巧。

---

## 示例概览

本目录包含 **10+ 个核心示例**，涵盖宏系统的所有重要主题：

- ✅ 声明宏基础 (`macro_rules!`)
- ✅ 模式匹配与重复
- ✅ 递归宏 (TT muncher)
- ✅ 宏的卫生性
- ✅ Rust 版本特性演示
- ✅ 真实应用场景

---

## 示例分类导航

### 声明宏 ⭐

适合了解声明宏基础的开发者。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `01_macro_rules_basics.rs` | 声明宏基础 | `macro_rules!` | `cargo run --example 01_macro_rules_basics` |
| `02_pattern_matching.rs` | 模式匹配 | 匹配规则 | `cargo run --example 02_pattern_matching` |
| `03_repetition.rs` | 重复模式 | `$()*` | `cargo run --example 03_repetition` |

### 高级声明宏 ⭐⭐

适合需要深入理解宏机制的开发者。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `04_recursive_macros.rs` | 递归宏 | TT muncher | `cargo run --example 04_recursive_macros` |

### Rust 版本特性示例 ⭐ NEW

展示最新 Rust 版本的宏相关改进。

| 示例 | 描述 | 核心概念 | 运行命令 |
|------|------|----------|----------|
| `rust_192_features_demo.rs` | Rust 1.93.0 特性演示 | `rotate_right`、性能监控 | `cargo run --example rust_192_features_demo` |
| `rust_191_features_demo.rs` | Rust 1.91 特性演示 | 宏展开缓存 | `cargo run --example rust_191_features_demo` |
| `rust_190_features_demo.rs` | Rust 1.90 特性演示 | 历史参考 | `cargo run --example rust_190_features_demo` |

---

## 如何运行示例

### 基础运行

```bash
# 进入模块目录
cd crates/c11_macro_system

# 运行声明宏基础示例
cargo run --example 01_macro_rules_basics

# 运行模式匹配示例
cargo run --example 02_pattern_matching

# 运行重复模式示例
cargo run --example 03_repetition

# 运行递归宏示例
cargo run --example 04_recursive_macros
```

### 查看宏展开

```bash
# 安装 cargo-expand（如果尚未安装）
cargo install cargo-expand

# 查看宏展开结果
cargo expand --example 01_macro_rules_basics
cargo expand --example 02_pattern_matching
cargo expand --example 03_repetition
cargo expand --example 04_recursive_macros
```

### 运行 Rust 版本特性示例

```bash
# Rust 1.93.0 特性演示
cargo run --example rust_192_features_demo

# Rust 1.91 特性演示（历史参考）
cargo run --example rust_191_features_demo

# Rust 1.90 特性演示（历史参考）
cargo run --example rust_190_features_demo
```

### 运行测试

```bash
# 运行所有测试
cargo test -p c11_macro_system

# 运行声明宏测试
cargo test declarative_tests

# 运行过程宏测试（在 proc crate 中）
cargo test -p c11_macro_system_proc
```

---

## 学习建议

### 初学者路径 (第1-2周)

1. **学习声明宏基础**

   ```bash
   cargo run --example 01_macro_rules_basics
   ```

   - `macro_rules!` 语法
   - 基本模式匹配
   - 简单替换

2. **掌握模式匹配**

   ```bash
   cargo run --example 02_pattern_matching
   ```

   - 片段分类符 (`expr`, `ty`, `ident` 等)
   - 多重匹配分支
   - 捕获组

3. **学习重复模式**

   ```bash
   cargo run --example 03_repetition
   ```

   - `$()*` - 零次或多次
   - `$()+` - 一次或多次
   - `$()?` - 零次或一次
   - 分隔符处理

### 进阶路径 (第3-4周)

1. **理解递归宏**

   ```bash
   cargo run --example 04_recursive_macros
   ```

   - TT muncher 模式
   - 递归终止条件
   - 复杂 token 处理

2. **探索宏卫生性**
   - 宏内部作用域
   - 变量捕获规则
   - `tt` 与 `item` 区别

### 高级路径 (第5周+)

1. **学习过程宏**
   - 派生宏 (`#[derive(Trait)]`)
   - 属性宏 (`#[attribute]`)
   - 函数宏 (`custom!()`)

   > **注意**: 过程宏必须在独立的 proc-macro crate 中编译。参考 `src/proc/` 目录中的实现。

2. **Rust 1.93.0 新特性**

   ```bash
   cargo run --example rust_192_features_demo
   ```

   - `rotate_right` 在宏展开队列中的应用
   - `NonZero::div_ceil` 在宏缓存中的应用
   - 宏展开性能监控

---

## 关键概念速查

### 声明宏基础

```rust
// 简单宏
macro_rules! say_hello {
    () => { println!("Hello!"); };
}

// 带参数
macro_rules! create_function {
    ($name:ident) => {
        fn $name() { println!("{:?}", stringify!($name)); }
    };
}

// 重复模式
macro_rules! print_all {
    ($($arg:expr),*) => {
        $(println!("{}", $arg);)*
    };
}

// 带分隔符的重复
macro_rules! vec_mac {
    ($($x:expr),* $(,)?) => {
        {
            let mut temp_vec = Vec::new();
            $(temp_vec.push($x);)*
            temp_vec
        }
    };
}
```

### 片段分类符

| 分类符 | 匹配内容 | 示例 |
|--------|----------|------|
| `ident` | 标识符 | `foo`, `bar`, `x` |
| `expr` | 表达式 | `1 + 2`, `foo()` |
| `ty` | 类型 | `i32`, `Vec<T>` |
| `pat` | 模式 | `Some(x)`, `1..=5` |
| `stmt` | 语句 | `let x = 1;` |
| `block` | 代码块 | `{ let x = 1; x }` |
| `item` | 项 | `fn`, `struct`, `use` |
| `meta` | 属性内容 | `derive(Debug)` |
| `tt` | Token 树 | 任何单个 token 或括号组 |
| `lifetime` | 生命周期 | `'a`, `'static` |
| `literal` | 字面量 | `"hello"`, `42` |
| `path` | 路径 | `std::vec::Vec` |

### 递归宏 (TT Muncher)

```rust
macro_rules! print_all_tts {
    // 基本情况：没有更多 token
    () => {};
    // 处理一个 token，递归处理剩余部分
    ($first:tt $($rest:tt)*) => {
        print!("{:?} ", stringify!($first));
        print_all_tts!($($rest)*);
    };
}

// 使用
print_all_tts!(fn main() { println!("hello"); });
```

### 宏的卫生性

```rust
macro_rules! using_a {
    ($e:expr) => {
        {
            let a = 42;
            $e
        }
    };
}

let four = using_a!(a / 10); // 错误！宏内部的 a 在外部不可见
```

### 常用宏模式

```rust
// 1. 简单替换
macro_rules! const_str {
    ($name:ident, $value:expr) => {
        const $name: &str = $value;
    };
}

// 2. 委托实现
macro_rules! impl_display {
    ($type:ty) => {
        impl std::fmt::Display for $type {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:?}", self)
            }
        }
    };
}

// 3. 枚举变体生成
macro_rules! enum_with_variants {
    ($name:ident { $($variant:ident),* $(,)? }) => {
        pub enum $name {
            $($variant),*
        }
    };
}

// 4. 测试生成
macro_rules! test_cases {
    ($($name:ident: $value:expr),* $(,)?) => {
        $(
            #[test]
            fn $name() {
                assert!($value);
            }
        )*
    };
}
```

---

## 过程宏说明

### 主 Crate 与 Proc 模块关系

- **主 crate** (`c11_macro_system`): 导出 `declarative`（声明宏）、`utils`、Rust 1.91/1.92/1.93 特性
- **proc 模块** (`src/proc/`): 包含过程宏实现（Builder、debug_print、timed 等）

> **注意**: Rust 要求过程宏必须在**独立的 proc-macro crate** 中编译。当前 `src/proc/` 为**参考实现**，供学习过程宏写法；若要在项目中使用，需将其拆分为独立 crate（如 `c11_macro_system_proc`）并设置 `[lib] proc-macro = true`。

### 过程宏类型

```rust
// 派生宏
#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    // ...
}

// 属性宏
#[proc_macro_attribute]
pub fn route(args: TokenStream, input: TokenStream) -> TokenStream {
    // ...
}

// 函数宏
#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    // ...
}
```

---

## 相关文档

### 模块文档

- [模块主页](../README.md) - 完整学习指南
- [文档中心](../docs/README.md) - 详细文档导航
- [主索引](../docs/00_MASTER_INDEX.md) - 文档完整索引
- [术语表](../docs/Glossary.md) - 核心术语
- [FAQ](../docs/FAQ.md) - 常见问题

### 分层文档

- [Tier 1: 基础层](../docs/tier_01_foundations/) - 宏理论基础
- [Tier 2: 实践层](../docs/tier_02_guides/) - 声明宏+过程宏实践
- [Tier 3: 参考层](../docs/tier_03_references/) - 最佳实践参考
- [Tier 4: 高级层](../docs/tier_04_advanced/) - DSL/调试/优化

### 外部资源

- [The Rust Book - 宏](https://doc.rust-lang.org/book/ch19-06-macros.html)
- [The Rust Reference - 宏](https://doc.rust-lang.org/reference/macros.html)
- [The Little Book of Rust Macros](https://veykril.github.io/tlborm/) - 宏权威指南
- [proc-macro-workshop](https://github.com/dtolnay/proc-macro-workshop) - 过程宏练习
- [syn 文档](https://docs.rs/syn/)
- [quote 文档](https://docs.rs/quote/)

---

## 宏设计原则

### 最佳实践

```rust
// ✅ 好的宏：清晰意图
macro_rules! with_timer {
    ($name:expr, $body:block) => {{
        let start = std::time::Instant::now();
        let result = $body;
        println!("{} took {:?}", $name, start.elapsed());
        result
    }};
}

// ✅ 好的宏：提供良好的错误信息
macro_rules! ensure {
    ($cond:expr, $msg:expr) => {
        if !$cond {
            panic!("Assertion failed: {}", $msg);
        }
    };
}

// ✅ 好的宏：避免过于复杂的递归
// 复杂逻辑考虑使用过程宏
```

### 常见模式总结

| 模式 | 用途 | 示例 |
|------|------|------|
| 简单替换 | 代码简化 | `say_hello!()` |
| 参数化 | 生成代码 | `create_function!` |
| 重复 | 处理列表 | `vec!`, `hashmap!` |
| 递归 | 复杂处理 | TT muncher |
| DSL | 领域语言 | `sql!`, `html!` |
| 委托 | 实现 trait | `impl_display!` |
| 测试生成 | 批量测试 | `test_cases!` |

---

## 调试技巧

```rust
// 使用 compile_error! 在编译期生成错误
macro_rules! check_feature {
    ($feature:tt) => {
        #[cfg(not(feature = $feature))]
        compile_error!(concat!("Feature ", stringify!($feature), " is required"));
    };
}

// 使用 dbg! 宏调试
macro_rules! debug_macro {
    ($($tokens:tt)*) => {{
        let result = $($tokens)*;
        dbg!(&result);
        result
    }};
}
```

---

*示例基于 Rust 1.94+，Edition 2024*:

[返回模块主页](../README.md) | [返回上级](../README.md)
