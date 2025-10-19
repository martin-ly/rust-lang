# C03 控制流与函数: 主索引 (Master Index)

> **文档定位**: 控制流与函数学习路径总导航，涵盖条件、循环、模式匹配、闭包等  
> **使用方式**: 作为学习起点，根据需求选择合适的学习路径和文档  
> **相关文档**: [README](../README.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 导航索引

---

## 📋 快速导航

### 🎯 按角色导航

| 角色 | 推荐路径 | 关键文档 |
|------|---------|---------|
| **初学者** | 基础控制流 → 条件表达式 → 循环结构 | [02_basics/](./02_basics/) |
| **中级开发者** | 模式匹配 → 闭包 → 错误处理 | [03_advanced/](./03_advanced/) |
| **架构师** | 高级控制流 → 性能优化 → 设计模式 | [04_practice/](./04_practice/) |
| **研究者** | 理论基础 → 类型系统 → Rust特性 | [01_theory/](./01_theory/) |

### 📚 按主题导航

| 主题 | 文档入口 | 说明 |
|------|---------|------|
| **概览** | [DOCUMENTATION_INDEX.md](./DOCUMENTATION_INDEX.md) | 完整文档索引 |
| **FAQ** | [FAQ.md](./FAQ.md) | 常见问题解答 |
| **术语表** | [Glossary.md](./Glossary.md) | 核心概念速查 |

---

## 🏗️ 核心内容结构

### 第一部分：理论基础

#### 1. 理论基础 (01_theory/)

| 文档 | 说明 |
|------|------|
| [控制流基础](./01_theory/01_control_flow_foundations.md) | 控制流理论基础 |
| [类型系统集成](./01_theory/02_type_system_integration.md) | 与类型系统的关系 |
| [所有权与控制流](./01_theory/03_ownership_control_flow.md) | 所有权在控制流中的作用 |

### 第二部分：基础知识

#### 2. 基础控制流 (02_basics/)

| 文档 | 说明 |
|------|------|
| [控制流基础](./02_basics/01_control_flow_fundamentals.md) | if/else、循环基础 |
| [条件表达式](./02_basics/02_conditional_expressions.md) | if/else 详解 |
| [迭代结构](./02_basics/03_iterative_constructs.md) | loop/while/for |
| [函数与闭包](./02_basics/04_functions_and_closures.md) | 函数定义与闭包基础 |
| [错误处理控制流](./02_basics/05_error_handling_as_control_flow.md) | Result/Option/?运算符 |
| [控制流总览 1.90](./02_basics/06_control_flow_overview_1_90.md) | Rust 1.90特性 |

### 第三部分：高级主题

#### 3. 高级控制流 (03_advanced/)

| 文档 | 说明 | Rust版本 |
|------|------|----------|
| [高级控制流](./03_advanced/01_advanced_control_flow.md) | 高级技巧 | 1.90+ |
| [模式匹配高级](./03_advanced/02_pattern_matching_advanced_1_90.md) | match 深度使用 | 1.90+ |
| [Match 人体工程学](./03_advanced/03_match_ergonomics_and_binding_1_90.md) | 绑定模式 | 1.90+ |
| [Let-Else 模式](./03_advanced/04_let_else_patterns_handbook_1_90.md) | let-else 语法 | 1.90+ |
| [标签块与Break值](./03_advanced/05_labeled_blocks_and_break_values_1_90.md) | 带标签的块 | 1.90+ |
| [闭包与Fn Traits](./03_advanced/06_closures_and_fn_traits_1_90.md) | 闭包深入 | 1.90+ |
| [循环与迭代器](./03_advanced/07_loops_and_iterators_control_1_90.md) | 迭代器控制 | 1.90+ |
| [Never类型实践](./03_advanced/08_never_type_practices_1_90.md) | ! 类型 | 1.90+ |
| [Try块高级](./03_advanced/09_try_blocks_advanced_1_90.md) | try 块 | 1.90+ |
| [While If Let链](./03_advanced/10_while_if_let_chains_1_90.md) | 链式匹配 | 1.90+ |

### 第四部分：实践应用

#### 4. 实践指南 (04_practice/)

| 文档 | 说明 |
|------|------|
| [函数与闭包实践](./04_practice/01_functions_closures_practice.md) | 实际应用 |
| [错误处理实践](./04_practice/02_error_handling_practice.md) | 错误处理模式 |
| [性能实践](./04_practice/03_control_flow_performance_practices_1_90.md) | 性能优化 |
| [设计模式](./04_practice/04_control_flow_design_patterns.md) | 常见模式 |
| [常见陷阱](./04_practice/05_common_pitfalls.md) | 避坑指南 |

### 第五部分：Rust 特性

#### 5. 版本特性 (05_rust_features/)

| 文档 | 版本 | 说明 |
|------|------|------|
| [Rust 1.89 基础语法](./05_rust_features/RUST_189_BASIC_SYNTAX_COMPREHENSIVE_GUIDE.md) | 1.89 | 完整语法指南 |
| [Rust 1.89 控制流](./05_rust_features/RUST_189_CONTROL_FLOW_FUNCTIONS_FULL_GUIDE.md) | 1.89 | 控制流完整指南 |
| [Rust 1.89 增强特性](./05_rust_features/RUST_189_ENHANCED_FEATURES.md) | 1.89 | 增强功能 |
| [Rust 1.90 特性总结](./05_rust_features/RUST_190_FEATURES_SUMMARY.md) | 1.90 | 新特性总结 |

---

## 📖 实践示例

### 可运行示例 (examples/)

```bash
# 查看示例目录
cd crates/c03_control_fn/examples

# 运行控制流示例
cargo run --example control_flow_demo

# 运行闭包示例
cargo run --example closure_demo
```

---

## 🧪 测试与验证

### 测试套件 (tests/)

```bash
# 运行所有测试
cargo test -p c03_control_fn

# 运行特定测试
cargo test --test control_flow_tests
```

---

## 📚 学习路径

### 🚀 初学者路径 (2-3周)

**Week 1: 基础概念**:

1. [控制流基础](./02_basics/01_control_flow_fundamentals.md)
2. [条件表达式](./02_basics/02_conditional_expressions.md)
3. [迭代结构](./02_basics/03_iterative_constructs.md)

**Week 2: 函数与错误**:

1. [函数与闭包](./02_basics/04_functions_and_closures.md)
2. [错误处理控制流](./02_basics/05_error_handling_as_control_flow.md)

**Week 3: 新特性与实践**:

1. [控制流总览 1.90](./02_basics/06_control_flow_overview_1_90.md)
2. [函数与闭包实践](./04_practice/01_functions_closures_practice.md)

### 🎓 中级路径 (3-4周)

**Week 1-2: 高级控制流**:

1. [高级控制流](./03_advanced/01_advanced_control_flow.md)
2. [模式匹配高级](./03_advanced/02_pattern_matching_advanced_1_90.md)
3. [Match 人体工程学](./03_advanced/03_match_ergonomics_and_binding_1_90.md)
4. [Let-Else 模式](./03_advanced/04_let_else_patterns_handbook_1_90.md)

**Week 3: 函数特性**:

1. [闭包与Fn Traits](./03_advanced/06_closures_and_fn_traits_1_90.md)
2. [循环与迭代器](./03_advanced/07_loops_and_iterators_control_1_90.md)

**Week 4: 特殊类型**:

1. [Never类型实践](./03_advanced/08_never_type_practices_1_90.md)
2. [Try块高级](./03_advanced/09_try_blocks_advanced_1_90.md)

### 🔬 高级路径 (4-6周)

**理论与实践**:

1. [理论基础](./01_theory/) - 所有理论文档
2. [高级主题](./03_advanced/) - 所有高级文档
3. [实践应用](./04_practice/) - 所有实践文档
4. [性能优化](./04_practice/03_control_flow_performance_practices_1_90.md)

---

## 🎯 按场景导航

### 控制流选择

| 需求 | 推荐方案 | 文档 |
|------|---------|------|
| 条件分支 | if/else、match | [02_basics/02](./02_basics/02_conditional_expressions.md) |
| 循环迭代 | for、while、loop | [02_basics/03](./02_basics/03_iterative_constructs.md) |
| 模式匹配 | match、if let | [03_advanced/02](./03_advanced/02_pattern_matching_advanced_1_90.md) |
| 错误处理 | Result、?运算符 | [02_basics/05](./02_basics/05_error_handling_as_control_flow.md) |

### 函数编程

| 需求 | 推荐方案 | 文档 |
|------|---------|------|
| 高阶函数 | 闭包、Fn traits | [03_advanced/06](./03_advanced/06_closures_and_fn_traits_1_90.md) |
| 函数组合 | 组合子、链式调用 | [04_practice/01](./04_practice/01_functions_closures_practice.md) |
| 惰性求值 | 迭代器 | [03_advanced/07](./03_advanced/07_loops_and_iterators_control_1_90.md) |

---

## 🔗 相关资源

### 项目文档

- [顶层 README](../README.md) - 项目概述
- [文档标准](./DOCUMENTATION_STANDARD.md) - 文档规范
- [文档索引](./DOCUMENTATION_INDEX.md) - 详细索引

### 工具与配置

- **Cargo.toml**: 依赖配置
- **examples/**: 示例代码
- **tests/**: 测试用例

---

## 📊 项目统计

### 文档规模

- **理论文档**: 3 个
- **基础文档**: 6 个
- **高级文档**: 10 个
- **实践文档**: 5 个
- **特性文档**: 4+ 个

### 内容覆盖

- **控制流结构**: if/match/loop/for/while
- **函数特性**: 闭包、高阶函数、Fn traits
- **错误处理**: Result/Option/?运算符
- **Rust 1.90**: let-else、if-let链、Never类型

---

## 🆕 最新更新

### 2025-10-19

- ✅ 创建主索引文档
- ✅ 完善导航结构
- ✅ 统一文档格式

### Rust 1.90 特性

- ✅ let-else 模式
- ✅ if-let 链
- ✅ Never 类型稳定化
- ✅ 模式匹配增强

---

## 📞 获取帮助

### 问题解决

1. **查看 FAQ**: [FAQ.md](./FAQ.md) - 常见问题解答
2. **查看术语表**: [Glossary.md](./Glossary.md) - 核心概念定义
3. **查看示例**: examples/ - 可运行的示例代码
4. **运行测试**: `cargo test` - 验证功能

### 社区支持

- **GitHub Issues**: 报告问题和建议
- **代码审查**: 提交 PR 获得反馈
- **技术讨论**: 参与社区讨论

---

**文档维护**: Rust 学习社区  
**更新频率**: 跟随项目进度持续更新  
**文档版本**: v1.0  
**Rust 版本**: 1.90+
