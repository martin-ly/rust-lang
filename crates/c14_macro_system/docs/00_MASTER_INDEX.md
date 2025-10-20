# 📖 C14宏系统 - 主索引

> **学习导航**: C14宏系统模块的完整学习路径和资源导航  
> **最后更新**: 2025-10-20  
> **适用版本**: Rust 1.90+

---

## 🎯 模块概述

Rust宏系统是一个强大的元编程框架，允许在编译期进行代码生成和转换。本模块提供从基础到高级的系统化学习内容。

### 学习目标

完成本模块后，你将能够：

- ✅ 理解宏的基本概念和工作原理
- ✅ 使用`macro_rules!`编写声明宏
- ✅ 实现三种类型的过程宏
- ✅ 构建领域特定语言(DSL)
- ✅ 调试和优化宏性能

---

## 📚 学习路径

### 🌱 初学者路径 (2-3周)

#### Week 1: 宏基础

**第1天-2天: 理论基础**:

- [ ] [宏基础理论](./01_theory/01_macro_fundamentals.md)
- [ ] [卫生宏与作用域](./01_theory/02_hygiene_and_scope.md)
- [ ] 运行示例: `01_macro_rules_basics.rs`

**第3天-4天: 声明宏入门**:

- [ ] [macro_rules!基础](./02_declarative/01_macro_rules_basics.md)
- [ ] [模式匹配](./02_declarative/02_pattern_matching.md)
- [ ] 运行示例: `02_pattern_matching.rs`

**第5天-7天: 声明宏进阶**:

- [ ] [重复语法](./02_declarative/03_repetition_syntax.md)
- [ ] [高级模式](./02_declarative/04_advanced_patterns.md)
- [ ] 运行示例: `03_repetition.rs`

#### Week 2-3: 递归宏与实践

**Week 2**:

- [ ] [递归宏](./02_declarative/05_recursive_macros.md)
- [ ] 运行示例: `04_recursive_macros.rs`
- [ ] 完成练习: 实现5个自定义宏

**Week 3**:

- [ ] [常用模式](./05_practice/01_common_patterns.md)
- [ ] [最佳实践](./05_practice/02_best_practices.md)
- [ ] 项目实战: 创建宏库

### 🚀 进阶路径 (3-4周)

#### Week 4-5: 过程宏

**派生宏 (Derive Macros)**:

- [ ] [过程宏基础](./03_procedural/01_proc_macro_basics.md)
- [ ] [派生宏](./03_procedural/02_derive_macros.md)
- [ ] 实践: 实现Builder派生宏

**属性宏 (Attribute Macros)**:

- [ ] [属性宏](./03_procedural/03_attribute_macros.md)
- [ ] 实践: 实现路由属性宏

**函数式宏 (Function-like Macros)**:

- [ ] [函数式宏](./03_procedural/04_function_macros.md)
- [ ] 实践: 实现SQL查询宏

**Token流处理**:

- [ ] [Token流](./03_procedural/05_token_streams.md)

#### Week 6-7: 高级应用

**DSL构建**:

- [ ] [DSL构建技术](./04_advanced/01_dsl_construction.md)
- [ ] 实践: 实现配置DSL

**代码生成**:

- [ ] [代码生成](./04_advanced/02_code_generation.md)
- [ ] [性能考量](./04_advanced/04_performance_considerations.md)

**调试与测试**:

- [ ] [宏调试](./04_advanced/03_macro_debugging.md)
- [ ] [宏测试](./04_advanced/05_macro_testing.md)

---

## 📖 文档结构

### 01_theory/ - 理论基础

| 文档 | 难度 | 预计时间 |
|------|------|---------|
| [01_macro_fundamentals.md](./01_theory/01_macro_fundamentals.md) | ⭐ | 2小时 |
| [02_hygiene_and_scope.md](./01_theory/02_hygiene_and_scope.md) | ⭐⭐ | 2小时 |
| [03_expansion_mechanism.md](./01_theory/03_expansion_mechanism.md) | ⭐⭐ | 3小时 |
| [04_macro_theory.md](./01_theory/04_macro_theory.md) | ⭐⭐⭐ | 4小时 |

### 02_declarative/ - 声明宏

| 文档 | 难度 | 预计时间 |
|------|------|---------|
| [01_macro_rules_basics.md](./02_declarative/01_macro_rules_basics.md) | ⭐ | 2小时 |
| [02_pattern_matching.md](./02_declarative/02_pattern_matching.md) | ⭐⭐ | 3小时 |
| [03_repetition_syntax.md](./02_declarative/03_repetition_syntax.md) | ⭐⭐ | 3小时 |
| [04_advanced_patterns.md](./02_declarative/04_advanced_patterns.md) | ⭐⭐⭐ | 4小时 |
| [05_recursive_macros.md](./02_declarative/05_recursive_macros.md) | ⭐⭐⭐ | 4小时 |

### 03_procedural/ - 过程宏

| 文档 | 难度 | 预计时间 |
|------|------|---------|
| [01_proc_macro_basics.md](./03_procedural/01_proc_macro_basics.md) | ⭐⭐ | 3小时 |
| [02_derive_macros.md](./03_procedural/02_derive_macros.md) | ⭐⭐⭐ | 5小时 |
| [03_attribute_macros.md](./03_procedural/03_attribute_macros.md) | ⭐⭐⭐ | 5小时 |
| [04_function_macros.md](./03_procedural/04_function_macros.md) | ⭐⭐⭐ | 5小时 |
| [05_token_streams.md](./03_procedural/05_token_streams.md) | ⭐⭐⭐⭐ | 6小时 |

### 04_advanced/ - 高级主题

| 文档 | 难度 | 预计时间 |
|------|------|---------|
| [01_dsl_construction.md](./04_advanced/01_dsl_construction.md) | ⭐⭐⭐⭐ | 8小时 |
| [02_code_generation.md](./04_advanced/02_code_generation.md) | ⭐⭐⭐⭐ | 6小时 |
| [03_macro_debugging.md](./04_advanced/03_macro_debugging.md) | ⭐⭐⭐ | 4小时 |
| [04_performance_considerations.md](./04_advanced/04_performance_considerations.md) | ⭐⭐⭐ | 4小时 |
| [05_macro_testing.md](./04_advanced/05_macro_testing.md) | ⭐⭐⭐ | 4小时 |

### 05_practice/ - 最佳实践

| 文档 | 难度 | 预计时间 |
|------|------|---------|
| [01_common_patterns.md](./05_practice/01_common_patterns.md) | ⭐⭐ | 3小时 |
| [02_best_practices.md](./05_practice/02_best_practices.md) | ⭐⭐ | 3小时 |
| [03_anti_patterns.md](./05_practice/03_anti_patterns.md) | ⭐⭐ | 2小时 |
| [04_real_world_examples.md](./05_practice/04_real_world_examples.md) | ⭐⭐⭐ | 4小时 |

---

## 💻 代码示例

### 运行示例

```bash
# 查看所有示例
cargo run --example --list

# 运行特定示例
cargo run --example 01_macro_rules_basics
cargo run --example 02_pattern_matching
cargo run --example 03_repetition
cargo run --example 04_recursive_macros
```

### 示例列表

| 示例 | 主题 | 难度 |
|------|------|------|
| `01_macro_rules_basics.rs` | 声明宏基础 | ⭐ |
| `02_pattern_matching.rs` | 模式匹配 | ⭐⭐ |
| `03_repetition.rs` | 重复语法 | ⭐⭐ |
| `04_recursive_macros.rs` | 递归宏 | ⭐⭐⭐ |
| `05_derive_macro_demo.rs` | 派生宏 | ⭐⭐⭐ |
| `06_attribute_macro_demo.rs` | 属性宏 | ⭐⭐⭐ |
| `07_function_macro_demo.rs` | 函数式宏 | ⭐⭐⭐ |
| `08_dsl_example.rs` | DSL构建 | ⭐⭐⭐⭐ |

---

## 🎓 按角色导航

### 我是新手

**学习顺序**:

1. 从[宏基础理论](./01_theory/01_macro_fundamentals.md)开始
2. 学习[macro_rules!基础](./02_declarative/01_macro_rules_basics.md)
3. 运行示例 `01_macro_rules_basics.rs`
4. 查看[FAQ](./FAQ.md)解答疑惑

**推荐资源**:

- [快速参考](../README.md#快速参考)
- [术语表](./Glossary.md)

### 我有Rust基础

**快速通道**:

1. 浏览[理论文档](./01_theory/)
2. 直接学习[声明宏](./02_declarative/)
3. 完成所有基础示例
4. 进入[过程宏](./03_procedural/)学习

### 我想深入理解

**深度路径**:

1. 详细学习[宏理论](./01_theory/04_macro_theory.md)
2. 研究[展开机制](./01_theory/03_expansion_mechanism.md)
3. 掌握[Token流](./03_procedural/05_token_streams.md)
4. 实践[DSL构建](./04_advanced/01_dsl_construction.md)

---

## 🔍 按主题导航

### 声明宏 (macro_rules!)

**核心文档**:

- [基础语法](./02_declarative/01_macro_rules_basics.md)
- [模式匹配](./02_declarative/02_pattern_matching.md)
- [递归实现](./02_declarative/05_recursive_macros.md)

**示例**:

- `01_macro_rules_basics.rs`
- `04_recursive_macros.rs`

### 过程宏 (Procedural Macros)

**三种类型**:

1. [派生宏](./03_procedural/02_derive_macros.md) - `#[derive(Trait)]`
2. [属性宏](./03_procedural/03_attribute_macros.md) - `#[attribute]`
3. [函数式宏](./03_procedural/04_function_macros.md) - `macro!()`

**示例**:

- `05_derive_macro_demo.rs`
- `06_attribute_macro_demo.rs`
- `07_function_macro_demo.rs`

### DSL与代码生成

**核心主题**:

- [DSL构建](./04_advanced/01_dsl_construction.md)
- [代码生成](./04_advanced/02_code_generation.md)

**示例**:

- `08_dsl_example.rs`
- `09_code_generation.rs`

---

## 🛠️ 工具与资源

### 开发工具

**cargo-expand** - 查看宏展开

```bash
cargo install cargo-expand
cargo expand --example 01_macro_rules_basics
```

**rust-analyzer** - IDE支持

- VSCode插件
- 宏展开提示
- 语法高亮

### 调试工具

**trace_macros** - 跟踪宏展开

```rust
#![feature(trace_macros)]
trace_macros!(true);
```

**log_syntax** - 打印语法

```rust
#![feature(log_syntax)]
```

---

## 📚 相关资源

### 官方文档

- [The Rust Book - Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)
- [The Rust Reference](https://doc.rust-lang.org/reference/macros.html)
- [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)

### 社区资源

- [proc-macro-workshop](https://github.com/dtolnay/proc-macro-workshop)
- [syn](https://docs.rs/syn/) - 语法解析
- [quote](https://docs.rs/quote/) - 代码生成

### 本模块资源

- [README](../README.md) - 模块总览
- [FAQ](./FAQ.md) - 常见问题
- [Glossary](./Glossary.md) - 术语表

---

## ✅ 学习检查清单

### 基础知识 (必须掌握)

- [ ] 理解宏与函数的区别
- [ ] 掌握`macro_rules!`基本语法
- [ ] 了解宏卫生(Hygiene)
- [ ] 能够编写简单的声明宏
- [ ] 理解模式匹配规则

### 进阶技能 (建议掌握)

- [ ] 实现递归宏
- [ ] 使用重复语法`$(...)*`
- [ ] 理解Token流概念
- [ ] 创建派生宏
- [ ] 实现属性宏

### 高级能力 (深入方向)

- [ ] 构建DSL
- [ ] 优化宏性能
- [ ] 调试复杂宏
- [ ] 设计宏API
- [ ] 在生产环境使用宏

---

## 🎯 下一步

根据你的学习目标选择：

1. **系统学习** → 按[初学者路径](#)开始
2. **快速上手** → 直接运行[示例代码](#运行示例)
3. **解决问题** → 查看[FAQ](./FAQ.md)
4. **深入理解** → 阅读[理论文档](./01_theory/)

---

**开始学习！** 🚀

从第一个示例开始：

```bash
cargo run --example 01_macro_rules_basics
```

**最后更新**: 2025-10-20  
**维护者**: Rust学习社区
