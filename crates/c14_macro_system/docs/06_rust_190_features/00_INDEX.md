# Rust 1.90 宏系统特性 - 索引

> **文档定位**: Rust 1.90宏系统特性的完整导航  
> **最后更新**: 2025-10-20

---


## 📊 目录

- [📚 文档列表](#文档列表)
  - [核心文档](#核心文档)
- [🎯 学习路径](#学习路径)
  - [初学者路径](#初学者路径)
  - [进阶路径](#进阶路径)
  - [专家路径](#专家路径)
- [📊 内容矩阵](#内容矩阵)
- [🔍 快速查找](#快速查找)
  - [按特性类型](#按特性类型)
  - [按使用场景](#按使用场景)
  - [按难度等级](#按难度等级)
- [📈 版本说明](#版本说明)
  - [Rust 1.90新特性](#rust-190新特性)
  - [向后兼容性](#向后兼容性)
- [🛠️ 实用工具](#️-实用工具)
  - [宏开发工具](#宏开发工具)
  - [依赖配置](#依赖配置)
- [📚 扩展阅读](#扩展阅读)
  - [相关文档](#相关文档)
  - [外部资源](#外部资源)
- [✅ 文档状态](#文档状态)
- [🤝 贡献指南](#贡献指南)
  - [文档维护](#文档维护)
  - [反馈与建议](#反馈与建议)
- [返回导航](#返回导航)


## 📚 文档列表

### 核心文档

1. **[README.md](README.md)** ⭐ 推荐起点
   - Rust 1.90宏系统特性指南
   - 10个主要特性板块
   - 难度: ⭐⭐⭐⭐

2. **[COMPREHENSIVE_FEATURES.md](COMPREHENSIVE_FEATURES.md)**
   - 完整特性清单
   - 稳定/实验/废弃特性
   - 版本兼容性矩阵
   - 难度: ⭐⭐⭐⭐

3. **[EXAMPLES.md](EXAMPLES.md)**
   - 可运行示例代码
   - 5个类别，15+个示例
   - 难度: ⭐⭐⭐

---

## 🎯 学习路径

### 初学者路径

1. 阅读 [README.md](README.md) 的前3节
   - 宏系统概述
   - 声明宏 1.90特性
   - 过程宏 1.90特性

2. 运行 [EXAMPLES.md](EXAMPLES.md) 的声明宏示例
   - 单位转换宏
   - 配置DSL
   - 日志宏

3. 查看最佳实践（README.md 第10节）

### 进阶路径

1. 深入 [COMPREHENSIVE_FEATURES.md](COMPREHENSIVE_FEATURES.md)
   - 所有稳定特性
   - 片段说明符完整列表
   - TokenStream API

2. 学习 [EXAMPLES.md](EXAMPLES.md) 的过程宏示例
   - Builder模式生成器
   - 自动Debug实现

3. 研究实验性特性

### 专家路径

1. 研究性能优化（README.md 第7节）
2. 掌握诊断与错误报告（README.md 第6节）
3. 实现综合应用（EXAMPLES.md 第5节）

---

## 📊 内容矩阵

| 主题 | README | COMPREHENSIVE | EXAMPLES |
|------|---------|---------------|----------|
| **声明宏基础** | ✅ 概述 | ✅ 详细列表 | ✅ 3个示例 |
| **派生宏** | ✅ 稳定化 | ✅ 完整API | ✅ 2个示例 |
| **属性宏** | ✅ 增强 | ✅ 所有位置 | ✅ 2个示例 |
| **函数式宏** | ✅ 改进 | ✅ 自定义语法 | ✅ 2个示例 |
| **TokenStream** | ✅ 改进 | ✅ 完整API | ✅ 操作示例 |
| **宏卫生性** | ✅ 增强 | ✅ Span保留 | ✅ 实例 |
| **诊断** | ✅ 错误报告 | ✅ 诊断API | ✅ 错误处理 |
| **性能** | ✅ 优化 | ✅ 基准 | ✅ 优化示例 |
| **工具链** | ✅ 支持 | ✅ 完整列表 | ✅ 使用示例 |
| **最佳实践** | ✅ 10条 | ✅ 优化建议 | ✅ 实战 |

---

## 🔍 快速查找

### 按特性类型

- **声明宏特性** → [README § 2](README.md#2-声明宏-macro_rules-190特性)
- **过程宏特性** → [README § 3](README.md#3-过程宏-190特性)
- **TokenStream API** → [COMPREHENSIVE § 1.3](COMPREHENSIVE_FEATURES.md#13-tokenstream-api)
- **实验性特性** → [COMPREHENSIVE § 2](COMPREHENSIVE_FEATURES.md#2-实验性特性)

### 按使用场景

- **Builder模式** → [EXAMPLES § 2.1](EXAMPLES.md#示例-21-builder模式生成器)
- **DSL构建** → [EXAMPLES § 4.1](EXAMPLES.md#示例-41-sql查询宏)
- **性能监控** → [EXAMPLES § 3.1](EXAMPLES.md#示例-31-性能监控宏)
- **路由系统** → [EXAMPLES § 5.1](EXAMPLES.md#示例-51-api路由注册系统)

### 按难度等级

- **⭐⭐ 入门** → README 前5节
- **⭐⭐⭐ 中级** → EXAMPLES 所有示例
- **⭐⭐⭐⭐ 高级** → COMPREHENSIVE 完整特性
- **⭐⭐⭐⭐⭐ 专家** → 实验性特性 + 性能优化

---

## 📈 版本说明

### Rust 1.90新特性

本目录重点关注Rust 1.90版本中的宏系统特性：

1. **完全稳定的过程宏** (1.30+)
2. **改进的错误诊断** (1.40+)
3. **TokenStream性能优化** (1.50+)
4. **syn 2.0生态支持** (1.56+)
5. **增强的宏卫生性** (1.70+)

### 向后兼容性

- ✅ 所有示例兼容 Rust 1.56+
- ✅ 核心特性兼容 Rust 1.30+
- ⚠️ 某些高级特性需要 Rust 1.70+

---

## 🛠️ 实用工具

### 宏开发工具

```bash
# 安装必备工具
cargo install cargo-expand  # 查看宏展开
cargo install cargo-udeps   # 检查未使用依赖

# 查看宏展开
cd crates/c14_macro_system
cargo expand

# 运行示例
cargo run --example 01_macro_rules_basics
```

### 依赖配置

```toml
# 过程宏开发依赖
[dependencies]
syn = { version = "2.0", features = ["full"] }
quote = "1.0"
proc-macro2 = "1.0"

[dev-dependencies]
trybuild = "1.0"  # 编译测试
```

---

## 📚 扩展阅读

### 相关文档

- [宏系统主索引](../00_MASTER_INDEX.md)
- [理论基础](../01_theory/)
- [声明宏教程](../02_declarative/)
- [过程宏教程](../03_procedural/)
- [最佳实践](../05_practice/)

### 外部资源

- [The Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)
- [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)
- [Proc Macro Workshop](https://github.com/dtolnay/proc-macro-workshop)
- [syn Documentation](https://docs.rs/syn/)
- [quote Documentation](https://docs.rs/quote/)

---

## ✅ 文档状态

| 文档 | 状态 | 完成度 | 最后更新 |
|------|------|--------|----------|
| README.md | ✅ 完成 | 100% | 2025-10-20 |
| COMPREHENSIVE_FEATURES.md | ✅ 完成 | 100% | 2025-10-20 |
| EXAMPLES.md | ✅ 完成 | 100% | 2025-10-20 |
| 00_INDEX.md | ✅ 完成 | 100% | 2025-10-20 |

---

## 🤝 贡献指南

### 文档维护

- 保持与最新Rust版本同步
- 确保所有示例可编译
- 添加更多实用示例

### 反馈与建议

如果您发现：

- 文档错误或过时信息
- 示例代码问题
- 需要补充的内容

请通过项目Issue反馈。

---

**索引版本**: v1.0  
**文档总计**: 4篇  
**示例总计**: 15+个  
**适用版本**: Rust 1.90+  
**维护状态**: ✅ 活跃

---

## 返回导航

- [返回主索引](../00_MASTER_INDEX.md)
- [C14宏系统README](../../README.md)
- [项目根目录](../../../../README.md)
