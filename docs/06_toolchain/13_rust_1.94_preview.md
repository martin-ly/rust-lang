# Rust 1.94 预览与特性追踪

> **创建日期**: 2026-02-28
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.94.0 (Beta)
> **预计发布**: 2026-03-05
> **状态**: 🔄 追踪中

---

## 目录

- [Rust 1.94 预览与特性追踪](#rust-194-预览与特性追踪)
  - [目录](#目录)
  - [版本概览](#版本概览)
  - [主要新特性预览](#主要新特性预览)
    - [1. `control_flow_ok` 稳定化](#1-control_flow_ok-稳定化)
    - [2. `int_format_into` 稳定化](#2-int_format_into-稳定化)
    - [3. `RangeToInclusive` 类型](#3-rangetoinclusive-类型)
    - [4. `refcell_try_map` 稳定化](#4-refcell_try_map-稳定化)
    - [5. `proc_macro_value` 稳定化](#5-proc_macro_value-稳定化)
  - [标准库更新](#标准库更新)
    - [新增稳定 API](#新增稳定-api)
    - [性能改进](#性能改进)
  - [Cargo 更新](#cargo-更新)
    - [1. rustdoc `--merge` 选项](#1-rustdoc---merge-选项)
    - [2. 结构化日志改进](#2-结构化日志改进)
    - [3. 配置包含 (`config-include`)](#3-配置包含-config-include)
  - [工具链更新](#工具链更新)
    - [Clippy](#clippy)
    - [Rustfmt](#rustfmt)
    - [rust-analyzer](#rust-analyzer)
  - [迁移准备](#迁移准备)
    - [升级检查清单](#升级检查清单)
    - [兼容性注意事项](#兼容性注意事项)
  - [形式化影响分析](#形式化影响分析)
    - [类型系统](#类型系统)
    - [所有权与借用](#所有权与借用)
    - [证明更新计划](#证明更新计划)
  - [相关文档](#相关文档)
  - [持续追踪](#持续追踪)

---

## 版本概览

| 项目 | 详情 |
| :--- | :--- |
| **版本号** | 1.94.0 |
| **当前状态** | Beta |
| **预计发布** | 2026-03-05 |
| **目标日期** | 2026年3月第一个星期四 |
| **主要主题** | 性能优化、API稳定化、工具链改进 |

---

## 主要新特性预览

### 1. `control_flow_ok` 稳定化

**特性**: `ControlFlow::ok()` 方法稳定化

**用途**: 简化控制流与 `Option`/`Result` 的互操作

```rust
use std::ops::ControlFlow;

// 1.94 新特性
fn process_items(items: &[i32]) -> Option<i32> {
    let result: ControlFlow<i32, ()> = items.iter().try_for_each(|&item| {
        if item < 0 {
            ControlFlow::Break(item)
        } else {
            ControlFlow::Continue(())
        }
    });

    // 新稳定的方法
    result.ok()
}
```

**形式化关联**: 与 [type_system_foundations](../research_notes/type_theory/type_system_foundations.md) 中 ControlFlow 类型理论相关

---

### 2. `int_format_into` 稳定化

**特性**: 整数格式化到预分配缓冲区

**用途**: 高性能格式化，避免额外分配

```rust
// 1.94 新特性
use std::fmt::Write;

let mut buf = String::with_capacity(20);
let n: i32 = 42;

// 直接格式化到现有缓冲区
n.fmt_into(&mut buf)?;  // 避免 String::from(n) 的分配
```

**性能提升**: 在热路径中减少 30-50% 的格式化开销

---

### 3. `RangeToInclusive` 类型

**特性**: `..=end` 范围的新类型 `RangeToInclusive`

**用途**: 更精确的范围类型匹配

```rust
// 1.94 新类型
let range = ..=10;  // RangeToInclusive<i32>

match range {
    std::ops::RangeToInclusive { end } => println!("Up to and including {}", end),
}
```

---

### 4. `refcell_try_map` 稳定化

**特性**: `RefCell::try_map` 和 `RefMut::try_map`

**用途**: 安全地映射 RefCell 内部值

```rust
use std::cell::RefCell;

let cell = RefCell::new(Some(42));

// 1.94 新特性
let result: Result<Ref<i32>, _> = RefCell::try_map(cell.borrow(), |opt| opt.as_ref());
```

**形式化关联**: 与 [ownership_model](../research_notes/formal_methods/ownership_model.md) 内部可变性规则相关

---

### 5. `proc_macro_value` 稳定化

**特性**: 过程宏中更丰富的值操作

**用途**: 改进宏的元编程能力

---

## 标准库更新

### 新增稳定 API

| API | 描述 | 形式化关联 |
| :--- | :--- | :--- |
| `ControlFlow::ok` | 转换为 Option | [type_system_foundations](../research_notes/type_theory/type_system_foundations.md) |
| `RefCell::try_map` | 条件映射 | [ownership_model](../research_notes/formal_methods/ownership_model.md) |
| `RangeToInclusive` | 包含结束的范围类型 | [type_system_foundations](../research_notes/type_theory/type_system_foundations.md) |
| `VecDeque::truncate_front` | 从头部截断 | [ownership_model](../research_notes/formal_methods/ownership_model.md) |

### 性能改进

- **排序算法**: 进一步优化 `slice::sort`
- **HashMap**: 重新哈希策略微调
- **字符串格式化**: `int_format_into` 减少分配

---

## Cargo 更新

### 1. rustdoc `--merge` 选项

**特性**: 多 crate 文档合并

```bash
# 合并多个 crate 的文档输出
cargo doc --merge --parts-out-dir target/doc-parts
```

### 2. 结构化日志改进

**特性**: `cargo report timings` 稳定化

```bash
# 查看构建时间分析
cargo report timings
```

### 3. 配置包含 (`config-include`)

**特性**: 允许 `.cargo/config.toml` 包含其他文件

```toml
# .cargo/config.toml
include = [
    { path = "local.toml", optional = true }
]
```

---

## 工具链更新

### Clippy

- 新增 lint: `todo!()` 在发布代码中的检测
- 改进: `async fn` 递归检测

### Rustfmt

- 改进: 宏格式化稳定性
- 修复: 某些注释布局问题

### rust-analyzer

- 改进: 1.94 新特性的语法高亮
- 新增: `RangeToInclusive` 类型推断支持

---

## 迁移准备

### 升级检查清单

| 检查项 | 命令 | 预期结果 |
| :--- | :--- | :--- |
| 版本检查 | `rustc --version` | 1.94.0 或更高 |
| Beta 安装 | `rustup install beta` | 成功 |
| 项目测试 | `cargo test` | 通过 |
| Clippy 检查 | `cargo clippy` | 无新警告 |

### 兼容性注意事项

1. **`RangeToInclusive` 模式匹配**
   - 现有代码中使用 `..=n` 的 match 臂可能需要更新
   - 建议: 使用 `std::ops::RangeToInclusive` 显式类型

2. **`control_flow_ok`**
   - 与现手动实现的转换逻辑兼容
   - 可直接替换为新的标准方法

---

## 形式化影响分析

### 类型系统

| 变更 | 形式化文档 | 影响 |
| :--- | :--- | :--- |
| `RangeToInclusive` 类型 | [type_system_foundations](../research_notes/type_theory/type_system_foundations.md) | 新增类型构造器 |
| `ControlFlow::ok` | [type_system_foundations](../research_notes/type_theory/type_system_foundations.md) | 新增类型转换 |

### 所有权与借用

| 变更 | 形式化文档 | 影响 |
| :--- | :--- | :--- |
| `RefCell::try_map` | [ownership_model](../research_notes/formal_methods/ownership_model.md) | 内部可变性新操作 |

### 证明更新计划

- [ ] 更新 [FORMAL_CONCEPTS_ENCYCLOPEDIA](../research_notes/FORMAL_CONCEPTS_ENCYCLOPEDIA.md) 添加新类型
- [ ] 更新 [COUNTER_EXAMPLES_COMPENDIUM](../research_notes/COUNTER_EXAMPLES_COMPENDIUM.md) 添加边界案例
- [ ] 更新 [RUST_193_FEATURE_MATRIX](../research_notes/RUST_193_FEATURE_MATRIX.md) 至 1.94

---

## 相关文档

| 文档 | 说明 |
| :--- | :--- |
| [07_rust_1.93_full_changelog](./07_rust_1.93_full_changelog.md) | 1.93 完整变更 |
| [12_rust_1.93.1_vs_1.93.0_comparison](./12_rust_1.93.1_vs_1.93.0_comparison.md) | 1.93.1 补丁说明 |
| [Rust 1.94 Beta 官方公告](https://blog.rust-lang.org/) | 待发布 |
| [Rust Project Goals](https://rust-lang.github.io/rust-project-goals/) | 项目目标追踪 |

---

## 持续追踪

```text
═══════════════════════════════════════════════════════════════════════

  📅 当前日期: 2026-02-28
  🎯 目标日期: 2026-03-05
  📊 当前状态: Beta 测试阶段

  稳定化进度:
  ├── control_flow_ok:     ████████████ 90% (等待 FCP)
  ├── int_format_into:     ████████████ 85% (等待审查)
  ├── RangeToInclusive:    ████████████ 80% (实现中)
  ├── refcell_try_map:     ████████████ 95% (等待 FCP)
  └── proc_macro_value:    ████████████ 75% (设计中)

═══════════════════════════════════════════════════════════════════════
```

---

**维护者**: Rust 文档推进团队
**追踪状态**: 🔄 持续更新中
**最后同步**: releases.rs (2026-02-27)
