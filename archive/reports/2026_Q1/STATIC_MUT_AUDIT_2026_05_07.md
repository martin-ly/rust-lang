# `static mut` 使用审计报告

> **审计日期**: 2026-05-07
> **Rust Edition**: 2024（`static mut` 引用已 deny-by-default）
> **审计范围**: `crates/` 和 `docs/` 目录
> **状态**: 🔴 需修复

---

## 目录

- [`static mut` 使用审计报告](.#static-mut-使用审计报告)
  - [目录](.#目录)
  - [审计结果摘要](.#审计结果摘要)
  - [需修复的文件清单](.#需修复的文件清单)
    - [🔴 源码级（编译失败）](.#-源码级编译失败)
    - [🟡 文档级（内容过时）](.#-文档级内容过时)
  - [迁移策略](.#迁移策略)
    - [计数器场景](.#计数器场景)
    - [延迟初始化场景](.#延迟初始化场景)
  - [修复优先级](.#修复优先级)

## 审计结果摘要

| 类别 | 数量 | 说明 |
|------|------|------|
| `src/` 源码中使用 | 6 处 | 直接影响编译（Edition 2024 下失败） |
| `tests/` 测试中使用 | 2 处 | 测试编译失败 |
| `examples/` 示例中使用 | 1 处 | 示例编译失败 |
| `docs/` 文档中使用 | 12 处 | 文档过时，误导读者 |

---

## 需修复的文件清单

### 🔴 源码级（编译失败）

| 文件路径 | 行号 | 上下文 | 建议修复 |
|---------|------|--------|---------|
| `c06_async/tests/archive/rust_190_comprehensive_tests.rs` | 66, 170 | `static mut COUNTER: usize = 0;` | 迁移至 `AtomicUsize` |
| `c06_async/src/bin/retry_backoff_exp01.rs` | 5 | `static mut COUNT: u32 = 0;` | 迁移至 `AtomicU32` |
| `c01_ownership_borrow_scope/examples/comprehensive_ownership_examples.rs` | 504 | `static mut INSTANCE: Option<Singleton> = None;` | 迁移至 `std::sync::OnceLock` |
| `c06_async/src/archive/async_control_flow_190.rs` | 368, 421 | `static mut COUNTER: usize = 0;` | 迁移至 `AtomicUsize` |
| `c13_embedded/examples/minimal_bare_metal.rs` | 33 | `static mut COUNTER: u32 = 0;` | 迁移至 `core::cell::Cell` 或原子类型 |
| `c02_type_system/src/advanced_macros.rs` | 182 | `static mut CACHE: Option<HashMap<...>> = None;` | 迁移至 `std::sync::OnceLock` |

### 🟡 文档级（内容过时）

| 文件路径 | 行号 | 上下文 |
|---------|------|--------|
| `c13_embedded/src/interrupt_handling.rs` | 46 | 注释中的 `static mut COUNTER` 示例 |
| `c01_ownership_borrow_scope/docs/tier_02_guides/06_代码示例集合.md` | 1240 | `static mut COUNTER: i32 = 0;` |
| `c05_threads/docs/tier_03_references/02_无锁编程参考.md` | 828 | `static mut DATA: i32 = 0;` |
| `c05_threads/docs/tier_02_guides/02_同步原语实践.md` | 923 | `static mut RESOURCE: Option<String> = None;` |
| `c03_control_fn/docs/tier_02_guides/02_循环结构指南.md` | 434, 895 | `static mut COUNTER`, `static mut INDEX` |
| `c11_macro_system/docs/tier_04_advanced/03_代码生成优化.md` | 483 | `static mut COUNTER: i32 = 0;` |
| `c02_type_system/docs/tier_03_references/05_性能优化参考.md` | 1004 | `static mut ALLOCATION_COUNT: usize = 0;` |
| `c02_type_system/docs/tier_01_foundations/04_常见问题.md` | 583 | `static mut COUNTER: i32 = 0;` |
| `c02_type_system/docs/tier_02_guides/05_生命周期指南.md` | 679, 702, 819 | 多处 `static mut` 示例 |
| `c07_process/docs/04_advanced_process_management.md` | 309 | `private static mut current_weight` |

---

## 迁移策略

### 计数器场景

```rust
// ❌ 旧代码
static mut COUNTER: i32 = 0;
unsafe { COUNTER += 1; }

// ✅ 新代码（线程安全）
use std::sync::atomic::{AtomicI32, Ordering};
static COUNTER: AtomicI32 = AtomicI32::new(0);
COUNTER.fetch_add(1, Ordering::Relaxed);

// ✅ 新代码（单线程/无 std）
use core::cell::Cell;
static COUNTER: Cell<i32> = Cell::new(0);
COUNTER.set(COUNTER.get() + 1);
```

### 延迟初始化场景

```rust
// ❌ 旧代码
static mut INSTANCE: Option<Singleton> = None;
unsafe {
    if INSTANCE.is_none() {
        INSTANCE = Some(Singleton::new());
    }
    INSTANCE.as_ref().unwrap()
}

// ✅ 新代码
use std::sync::OnceLock;
static INSTANCE: OnceLock<Singleton> = OnceLock::new();
INSTANCE.get_or_init(|| Singleton::new())
```

---

## 修复优先级

| 优先级 | 文件 | 原因 |
|--------|------|------|
| P0 | `c06_async/src/bin/retry_backoff_exp01.rs` | 可执行文件，直接影响运行 |
| P0 | `c01_ownership_borrow_scope/examples/...` | 示例代码，用户直接运行 |
| P1 | `c02_type_system/src/advanced_macros.rs` | 源码，影响库编译 |
| P1 | `c06_async/src/archive/...` | 归档代码，可能被引用 |
| P2 | 所有 `docs/` 文件 | 文档更新，不影响编译但误导读者 |
