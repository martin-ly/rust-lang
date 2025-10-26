# 🎯 C11: Rust宏系统 (Macro System)

## 🎯 2025-10-22 文档标准化完成 ✨

> **文档状态**: ✅ **100% 标准化完成**  
> **框架结构**: ✅ **4-Tier 架构**  
> **文档总数**: **36+ 篇**  
> **质量评分**: **95/100**

### 📖 新版文档导航

**从这里开始学习** ⭐:

- 🗺️ [完整索引](./docs/00_MASTER_INDEX.md)
- 📖 [术语表](./docs/Glossary.md)
- ❓ [常见问题](./docs/FAQ.md)

**文档层级结构**:

- 📚 [Tier 1: 基础层](./docs/tier_01_foundations/) - 宏理论
- 📝 [Tier 2: 实践层](./docs/tier_02_guides/) - 声明宏+过程宏
- 📖 [Tier 3: 参考层](./docs/tier_03_references/) - 最佳实践
- 🚀 [Tier 4: 高级层](./docs/tier_04_advanced/) - DSL/调试/优化

**标准化报告**: [C11_STANDARDIZATION_FINAL_2025_10_22.md](./docs/reports/C11_STANDARDIZATION_FINAL_2025_10_22.md)

---

> **模块定位**: Rust元编程和宏系统的系统化学习  
> **学习阶段**: 高级  
> **前置知识**: C02类型系统、C03控制流、C04泛型编程

**模块状态**: ✅ 标准化完成  
**最后更新**: 2025-10-22  
**Rust版本**: 1.90+

---

## 📋 模块概述

Rust宏系统是一个强大的元编程框架，允许在编译期进行代码生成和转换。
本模块提供从基础到高级的完整学习路径。

### 🎯 学习目标

完成本模块后，你将能够：

- ✅ 理解宏的基本概念和用途
- ✅ 使用`macro_rules!`编写声明宏
- ✅ 实现三种类型的过程宏
- ✅ 构建领域特定语言(DSL)
- ✅ 进行宏调试和性能优化
- ✅ 在生产环境中应用宏最佳实践

---

## 📚 核心内容

### 🔹 声明宏 (Declarative Macros)

使用`macro_rules!`定义的模式匹配宏：

```rust
macro_rules! vec_of_strings {
    ($($x:expr),*) => {
        vec![$($x.to_string()),*]
    };
}

let strings = vec_of_strings!["hello", "world"];
```

### 🔸 过程宏 (Procedural Macros)

**派生宏 (Derive Macros)**:

```rust
#[derive(Builder)]
struct Config {
    name: String,
    value: i32,
}
```

**属性宏 (Attribute Macros)**:

```rust
#[route(GET, "/api/users")]
fn get_users() -> Response { }
```

**函数式宏 (Function-like Macros)**:

```rust
let query = sql!("SELECT * FROM users WHERE id = ?");
```

---

## 🗂️ 模块结构

```text
C11_macro_system/
├── docs/                           # 📚 学习文档
│   ├── 00_MASTER_INDEX.md          # 主索引导航
│   ├── FAQ.md                      # 常见问题
│   ├── Glossary.md                 # 术语表
│   ├── 01_theory/                  # 理论基础
│   ├── 02_declarative/             # 声明宏
│   ├── 03_procedural/              # 过程宏
│   ├── 04_advanced/                # 高级主题
│   ├── 05_practice/                # 最佳实践
│   └── 06_rust_190_features/       # Rust 1.90特性
├── src/                            # 源代码
│   ├── declarative/                # 声明宏实现
│   └── utils/                      # 工具函数
├── proc_macros/                    # 过程宏crate
├── examples/                       # 示例代码
│   ├── 01_macro_rules_basics.rs
│   ├── 02_pattern_matching.rs
│   └── ...
├── tests/                          # 测试用例
└── benches/                        # 基准测试
```

---

## 🚀 快速开始

### 1. 查看文档

从主索引开始学习：

```bash
cat docs/00_MASTER_INDEX.md
```

### 2. 运行示例

```bash
# 声明宏基础
cargo run --example 01_macro_rules_basics

# 模式匹配
cargo run --example 02_pattern_matching

# 查看所有示例
cargo run --example --list
```

### 3. 运行测试

```bash
# 所有测试
cargo test

# 特定测试
cargo test declarative_tests
```

---

## 📖 学习路径

### 🌱 入门路径 (2-3周)

**Week 1: 宏基础**:

1. 阅读理论文档 → `docs/01_theory/`
2. 学习声明宏基础 → `docs/02_declarative/01_macro_rules_basics.md`
3. 实践基础示例 → `examples/01_*.rs`

**Week 2: 声明宏进阶**:

1. 模式匹配 → `docs/02_declarative/02_pattern_matching.md`
2. 递归宏 → `docs/02_declarative/05_recursive_macros.md`
3. 实现自己的宏

**Week 3: 过程宏入门**:

1. 过程宏基础 → `docs/03_procedural/01_proc_macro_basics.md`
2. 派生宏 → `docs/03_procedural/02_derive_macros.md`
3. 实践派生宏示例

### 🚀 进阶路径 (2-3周)

**Week 4-5: 过程宏深入**:

1. 属性宏和函数式宏
2. Token流处理
3. 复杂宏实现

**Week 6: 高级应用**:

1. DSL构建
2. 代码生成
3. 性能优化

---

## 🎓 前置知识

### 必需

- ✅ **C02 类型系统** - 理解类型在宏中的使用
- ✅ **C03 控制流** - 理解模式匹配
- ✅ **C04 泛型** - 理解泛型与宏的结合

### 推荐

- 📖 **C01 所有权** - 理解宏展开后的所有权
- 📖 **Rust基础语法** - 良好的Rust基础

---

## 💡 关键概念

### 宏的类型

| 类型 | 定义方式 | 用途 | 示例 |
|------|---------|------|------|
| 声明宏 | `macro_rules!` | 模式匹配代码生成 | `vec![]` |
| 派生宏 | `#[proc_macro_derive]` | 自动实现trait | `#[derive(Debug)]` |
| 属性宏 | `#[proc_macro_attribute]` | 修改或注解项 | `#[route(GET)]` |
| 函数宏 | `#[proc_macro]` | 函数式调用 | `sql!()` |

### 宏与函数的区别

```rust
// 函数 - 运行时执行
fn double(x: i32) -> i32 { x * 2 }

// 宏 - 编译期展开
macro_rules! double {
    ($x:expr) => { $x * 2 };
}
```

---

## 🛠️ 开发工具

### 宏展开查看

```bash
# 安装cargo-expand
cargo install cargo-expand

# 查看宏展开
cargo expand --example 01_macro_rules_basics
```

### 调试技巧

```rust
// 使用trace_macros
#![feature(trace_macros)]
trace_macros!(true);
```

---

## 📚 相关资源

### 官方文档

- [The Rust Book - Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)
- [The Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)
- [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)

### 本模块文档

- [主索引](./docs/00_MASTER_INDEX.md) - 完整学习导航
- [FAQ](./docs/FAQ.md) - 常见问题解答
- [术语表](./docs/Glossary.md) - 核心概念定义

### 实用工具

- [cargo-expand](https://github.com/dtolnay/cargo-expand) - 宏展开工具
- [syn](https://docs.rs/syn/) - 语法解析
- [quote](https://docs.rs/quote/) - 代码生成

---

## 🤝 贡献

欢迎贡献：

- 报告问题和错误
- 提供学习建议
- 分享实践经验
- 贡献示例代码

请查看 [贡献指南](../../CONTRIBUTING.md)

---

## 📊 学习统计

```text
📖 文档数量: 30+ 篇
💻 示例代码: 50+ 个
🧪 测试用例: 100+ 个
🎯 练习项目: 5+ 个
```

---

## ⚡ 快速参考

### 常用宏模式

```rust
// 1. 简单替换
macro_rules! say_hello {
    () => { println!("Hello!") };
}

// 2. 带参数
macro_rules! create_function {
    ($name:ident) => {
        fn $name() { println!("function {:?}", stringify!($name)); }
    };
}

// 3. 可变参数
macro_rules! print_all {
    ($($arg:expr),*) => {
        $(println!("{}", $arg);)*
    };
}

// 4. 递归
macro_rules! count {
    () => { 0 };
    ($x:expr) => { 1 };
    ($x:expr, $($rest:expr),*) => { 1 + count!($($rest),*) };
}
```

---

**开始你的宏学习之旅！** 🚀

从 [主索引](./docs/00_MASTER_INDEX.md) 开始，或直接运行第一个示例。

**最后更新**: 2025-10-20  
**维护者**: Rust学习社区  
**模块版本**: v0.1.0
