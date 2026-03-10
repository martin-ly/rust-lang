# C11 宏系统 - 文档中心

> **创建日期**: 2025-10-22
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 100% 完成
> **概念说明**: Rust 宏系统是强大的元编程工具，允许在编译期进行代码生成和转换。本文档涵盖声明宏 (macro_rules!)、过程宏 (派生宏、属性宏、函数宏) 以及高级宏技巧。

---

## 快速示例

```rust
// 声明宏基础
macro_rules! vec_mac {
    ($($x:expr),*) => {
        {
            let mut temp_vec = Vec::new();
            $(temp_vec.push($x);)*
            temp_vec
        }
    };
}

let v = vec_mac![1, 2, 3]; // 展开为 vec![1, 2, 3]

// 递归宏
macro_rules! count_args {
    () => { 0 };
    ($x:expr) => { 1 };
    ($x:expr, $($rest:expr),*) => { 1 + count_args!($($rest),*) };
}

// 模式匹配宏
macro_rules! create_function {
    ($name:ident) => {
        fn $name() {
            println!("function {:?} called", stringify!($name));
        }
    };
}

create_function!(foo);
create_function!(bar);
```

### 过程宏示例

```rust
// 派生宏
#[derive(Debug, Clone, Builder)]
struct Config {
    name: String,
    port: u16,
}

// 属性宏
#[route(GET, "/api/users")]
async fn get_users() -> Json<Vec<User>> {
    // ...
}

// 函数宏
let query = sql!("SELECT * FROM users WHERE id = ?", user_id);
```

---

## 文档结构导航

### 核心文档

| 文档 | 描述 | 难度 |
| :--- | :--- | :--- |
| [00_MASTER_INDEX.md](./00_MASTER_INDEX.md) | 主索引导航 | ⭐ |
| [ONE_PAGE_SUMMARY.md](./ONE_PAGE_SUMMARY.md) | 一页纸总结 | ⭐⭐ |
| [Glossary.md](./Glossary.md) | 术语表 | ⭐ |
| [FAQ.md](./FAQ.md) | 常见问题 | ⭐⭐ |

### Rust 版本特性文档

| 文档 | 描述 | 难度 |
| :--- | :--- | :--- |
| [RUST_192_MACRO_IMPROVEMENTS.md](./RUST_192_MACRO_IMPROVEMENTS.md) | Rust 1.93.0 宏系统改进 | ⭐⭐⭐ |
| [RUST_191_MACRO_IMPROVEMENTS.md](./RUST_191_MACRO_IMPROVEMENTS.md) | Rust 1.91 宏系统改进 | ⭐⭐⭐ |

### 分层文档结构

| 层级 | 路径 | 描述 | 时间 |
| :--- | :--- | :--- | :--- |
| Tier 1 | [tier_01_foundations/](./tier_01_foundations/) | 宏理论基础 | 2-4小时 |
| Tier 2 | [tier_02_guides/](./tier_02_guides/) | 声明宏+过程宏实践 | 10-20小时 |
| Tier 3 | [tier_03_references/](./tier_03_references/) | 最佳实践参考 | 按需 |
| Tier 4 | [tier_04_advanced/](./tier_04_advanced/) | DSL/调试/优化 | 20-30小时 |

---

## 核心概念概览

### 1. 声明宏 (Declarative Macros)

```rust
macro_rules! say_hello {
    () => { println!("Hello!"); };
}

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
macro_rules! hashmap {
    ($($key:expr => $value:expr),* $(,)?) => {
        {
            let mut map = ::std::collections::HashMap::new();
            $(map.insert($key, $value);)*
            map
        }
    };
}
```

### 2. 宏的卫生性 (Hygiene)

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

### 3. TT Muncher 模式

```rust
// 递归处理 token 树
macro_rules! print_all_tts {
    // 基本情况
    () => {};
    // 处理一个 token，递归处理剩余部分
    ($first:tt $($rest:tt)*) => {
        print!("{:?} ", stringify!($first));
        print_all_tts!($($rest)*);
    };
}

print_all_tts!(fn main() { println!("hello"); });
```

### 4. 过程宏类型

| 类型 | 属性 | 用途 | 示例 |
| :--- | :--- | :--- | :--- |
| 派生宏 | `#[derive(Trait)]` | 自动实现 trait | `#[derive(Debug)]` |
| 属性宏 | `#[attribute]` | 修改/注解项 | `#[route(GET, "/")]` |
| 函数宏 | `custom!()` | 函数式调用 | `sql!("SELECT...")` |

---

## 学习路径指引

### 路径 A: 入门学习 (2-3周)

**第1周: 声明宏基础**:

- 学习 `macro_rules!` 语法
- 理解模式匹配
- 掌握重复模式 (`$()*`)

**第2周: 声明宏进阶**:

- 学习递归宏 (TT muncher)
- 理解宏卫生性
- 实践复杂模式

**第3周: 过程宏入门**:

- 理解三种过程宏类型
- 学习 syn/quote crate
- 实践简单派生宏

### 路径 B: 深度学习 (4-6周)

在路径 A 基础上增加:

**第4-5周: 过程宏深入**:

- Token 流处理
- 语法树操作
- 复杂宏实现

**第6周: 高级应用**:

- DSL 构建
- 代码生成
- 性能优化

### 路径 C: 专家进阶 (持续)

**深入方向**:

- 编译器插件开发
- 元编程框架设计
- 形式化宏语义

---

## 开发工具

### 宏展开查看

```bash
# 安装 cargo-expand
cargo install cargo-expand

# 查看宏展开
cargo expand --example 01_macro_rules_basics
cargo expand --lib
```

### 调试技巧

```rust
// 使用 trace_macros (需要 nightly)
#![feature(trace_macros)]
trace_macros!(true);

// 使用 log_syntax! (需要 nightly)
#![feature(log_syntax)]
macro_rules! debug_print {
    ($($tok:tt)*) => { log_syntax!($($tok)*); };
}
```

### 关键 Crate

| Crate | 用途 | 版本 |
| :--- | :--- | :--- |
| syn | 语法解析 | 2.0+ |
| quote | 代码生成 | 1.0+ |
| proc-macro2 | Token 流处理 | 1.0+ |

---

## 思维表征工具

### 知识图谱

- **[多维概念矩阵](../../docs/04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md)** - 宏系统对比分析
- **[思维导图集合](../../docs/MIND_MAP_COLLECTION.md)** - 可视化知识结构
- **[决策图网](../../docs/04_thinking/DECISION_GRAPH_NETWORK.md)** - 宏类型选择决策
- **[证明图网](../../docs/04_thinking/PROOF_GRAPH_NETWORK.md)** - 宏展开正确性证明

### 宏类型决策树

```text
需要元编程？
├── 代码重复/模板化 → 声明宏 (macro_rules!)
└── 需要语法分析/生成
    ├── 为类型自动实现 trait → 派生宏
    ├── 修改/包装代码 → 属性宏
    └── 函数式代码生成 → 函数宏
```

---

## 形式化理论

深入学习宏系统的形式化理论基础：

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 宏系统形式化理论 | 展开规则 | [../../docs/rust-formal-engineering-system/01_theoretical_foundations/08_macro_system/](../../docs/rust-formal-engineering-system/01_theoretical_foundations/08_macro_system/) |
| 类型系统理论 | 宏中的类型操作 | [../../docs/rust-formal-engineering-system/01_theoretical_foundations/01_type_system/README.md](../../docs/rust-formal-engineering-system/01_theoretical_foundations/01_type_system/README.md) |
| 形式化验证理论 | 宏正确性验证 | [../../docs/rust-formal-engineering-system/01_theoretical_foundations/09_formal_verification/](../../docs/rust-formal-engineering-system/01_theoretical_foundations/09_formal_verification/) |
| 数学基础 | 元编程数学基础 | [../../docs/rust-formal-engineering-system/01_theoretical_foundations/10_mathematical_foundations/](../../docs/rust-formal-engineering-system/01_theoretical_foundations/10_mathematical_foundations/) |

---

## 相关资源

### 代码示例

```bash
# 运行声明宏示例
cargo run --example 01_macro_rules_basics
cargo run --example 02_pattern_matching
cargo run --example 03_repetition
cargo run --example 04_recursive_macros

# 运行版本特性示例
cargo run --example rust_191_features_demo
cargo run --example rust_192_features_demo
cargo run --example rust_193_features_demo
```

### 过程宏开发

```bash
# 查看派生宏展开
cargo expand --package c11_macro_system

# 运行测试
cargo test -p c11_macro_system
cargo test declarative_tests
```

### 外部资源

- [The Rust Book - 宏](https://doc.rust-lang.org/book/ch19-06-macros.html)
- [The Rust Reference - 宏](https://doc.rust-lang.org/reference/macros.html)
- [The Little Book of Rust Macros](https://veykril.github.io/tlborm/) - 宏权威指南
- [proc-macro-workshop](https://github.com/dtolnay/proc-macro-workshop) - 过程宏练习

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

// ❌ 避免：过于复杂的递归
// 考虑使用过程宏

// ✅ 好的宏：提供良好的错误信息
macro_rules! ensure {
    ($cond:expr, $msg:expr) => {
        if !$cond {
            panic!("Assertion failed: {}", $msg);
        }
    };
}
```

### 常见模式

| 模式 | 用途 | 示例 |
| :--- | :--- | :--- |
| 简单替换 | 代码简化 | `say_hello!()` |
| 参数化 | 生成代码 | `create_function!` |
| 重复 | 处理列表 | `vec!`, `hashmap!` |
| 递归 | 复杂处理 | TT muncher |
| DSL | 领域语言 | `sql!`, `html!` |

---

[返回模块主页](../README.md) | [返回文档中心](../../docs/README.md)
