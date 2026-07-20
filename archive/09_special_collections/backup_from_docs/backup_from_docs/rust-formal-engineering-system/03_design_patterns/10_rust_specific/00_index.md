# Rust特定模式（Rust-Specific Patterns）索引

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: 🔄 进行中

---

## 📊 目录

- [Rust特定模式（Rust-Specific Patterns）索引](#rust特定模式rust-specific-patterns索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心模式](#核心模式)
  - [Rust 化要点](#rust-化要点)
  - [术语（Terminology）](#术语terminology)
  - [实践与样例（Practice）](#实践与样例practice)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

---

## 目的

- 介绍 Rust 特有的设计模式。
- 提供利用 Rust 语言特性的最佳实践。

---

## 核心模式

- **RAII 模式（Resource Acquisition Is Initialization）**: 资源管理
- **Newtype 模式**: 类型安全包装
- **Builder 模式**: 构建复杂对象
- **Type State 模式**: 使用类型表示状态
- **零成本抽象模式**: 零运行时开销的抽象
- **错误处理模式**: `Result` 和 `?` 操作符
- **迭代器模式**: Rust 内置迭代器
- **闭包模式**: 函数式编程风格

---

## Rust 化要点

- **所有权系统**: 利用所有权系统管理资源
- **生命周期**: 使用生命周期注解管理引用
- **Trait 系统**: 使用 Trait 实现多态
- **模式匹配**: 使用 `match` 进行模式匹配
- **错误处理**: 使用 `Result` 类型处理错误

---

## 术语（Terminology）

- Rust特定模式（Rust-Specific Patterns）
- RAII、Newtype、Builder
- Type State、零成本抽象（Zero-Cost Abstraction）
- 错误处理（Error Handling）

---

## 实践与样例（Practice）

### 文件级清单（精选）

- 参见 [`crates/c01_ownership_borrow_scope/`](../../../../crates/c01_ownership_borrow_scope/) 目录
- 参见 [`crates/c02_type_system/`](../../../../crates/c02_type_system/) 目录
- 参见 [`crates/c09_design_pattern/`](../../../../crates/c09_design_pattern/) 目录

---

## 相关索引

- [所有权与借用](../../01_theoretical_foundations/03_ownership_borrowing/00_index.md)
- [类型系统](../../01_theoretical_foundations/01_type_system/00_index.md)
- [设计模式总索引](../00_index.md)

---

## 导航

- 返回总索引：[`../00_index.md`](../00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
- 所有权：[`../../01_theoretical_foundations/03_ownership_borrowing/00_index.md`](../../01_theoretical_foundations/03_ownership_borrowing/00_index.md)
