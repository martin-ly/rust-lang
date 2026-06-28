# TRPL 第三版（2024 Edition）对齐索引

> **分级**: [B]
> **版本**: TRPL 第三版（NoStarch 印刷版 / 在线版 2025+）
> **Rust 版本**: 1.85.0+ (Edition 2024)
> **最后更新**: 2026-06-01

---

## 使用说明

本索引将 The Rust Programming Language (TRPL) 第三版的章节结构与项目知识体系进行映射，帮助学习者：

1. 按 TRPL 顺序学习时，快速定位本项目的深度扩展内容
2. 按本项目路径学习时，了解与权威教材的对应关系

---

## 章节映射表

### Ch.1-6: 基础入门

| TRPL 章节 | 主题 | 本项目对应 | 补充深度 |
|:---|:---|:---|:---:|
| Ch.1 入门 | 安装、Hello World | [`concept/00_meta/learning_guide.md`](../../../../../concept/00_meta/learning_guide.md) | L0 学习路径 |
| Ch.2 猜数游戏 | 第一个项目 | [`exercises/src/`](../../exercises) | 练习系统 |
| Ch.3 通用概念 | 变量、类型、函数、控制流 | [`concept/01_foundation/`](../../../../../concept/01_foundation) | L1 基础层 |
| Ch.4 所有权 | Move/Copy/Clone/Drop | [`concept/01_foundation/01_ownership.md`](../../../../../concept/01_foundation/01_ownership.md) | 🔬 形式化语义 |
| Ch.5 结构体 | struct、impl、关联函数 | [`concept/01_foundation/04_type_system.md`](../../../../../concept/01_foundation/04_type_system.md) | 🔬 类型论差异 |
| Ch.6 枚举与模式 | enum、`Option<T>`、`match` | [`concept/01_foundation/04_type_system.md`](../../../../../concept/01_foundation/04_type_system.md) §枚举 | 🔬 代数数据类型 |

### Ch.7-10: 核心进阶

| TRPL 章节 | 主题 | 本项目对应 | 补充深度 |
|:---|:---|:---|:---:|
| Ch.7 模块系统 | `mod`、`use`、`pub`、crate | [`concept/06_ecosystem/01_toolchain.md`](../../../../../concept/06_ecosystem/01_toolchain.md) §Workspace | 📦 Cargo 高级特性 |
| Ch.8 常用集合 | `Vec`、`HashMap`、`String` | [`concept/01_foundation/08_collections.md`](../../../../../concept/01_foundation/08_collections.md) | 🔬 内存布局分析 |
| Ch.9 错误处理 | `Result<T,E>`、`?`、`panic!` | [`concept/02_intermediate/04_error_handling.md`](../../../../../concept/02_intermediate/04_error_handling.md) | 🔬 错误传播代数 |
| Ch.10 泛型、Trait、生命周期 | `<T>`、`trait`、`'a` | [`concept/02_intermediate/02_generics.md`](../../../../../concept/02_intermediate/02_generics.md) · [`concept/02_intermediate/01_traits.md`](../../../../../concept/02_intermediate/01_traits.md) · [`concept/01_foundation/03_lifetimes.md`](../../../../../concept/01_foundation/03_lifetimes.md) | 🔬 单态化、GATs、HRTB |

### Ch.11-16: 高级主题

| TRPL 章节 | 主题 | 本项目对应 | 补充深度 |
|:---|:---|:---|:---:|
| Ch.11 测试 | `#[test]`、集成测试 | [`concept/02_intermediate/05_assert_matches.md`](../../../../../concept/02_intermediate/05_assert_matches.md) | 🔬 `assert_matches!` (1.96.0) |
| Ch.12 I/O 项目 | 实用项目 | [`crates/c07_process/`](../../../../../crates/c07_process) | 📦 完整 crate |
| Ch.13 闭包与迭代器 | `Fn`/`FnMut`/`FnOnce`、`Iterator` | [`concept/02_intermediate/`](../../../../../concept/02_intermediate) | 🔬 迭代器组合子矩阵 |
| Ch.14 Cargo | crates.io、Workspace | [`concept/06_ecosystem/01_toolchain.md`](../../../../../concept/06_ecosystem/01_toolchain.md) | 📦 17-member workspace |
| Ch.15 智能指针 | `Box`、`Rc`、`Arc`、`RefCell` | [`concept/02_intermediate/03_memory_management.md`](../../../../../concept/02_intermediate/03_memory_management.md) | 🔬 内部可变性形式化 |
| Ch.16 无畏并发 | 线程、`Send`/`Sync`、消息传递 | [`concept/03_advanced/01_concurrency.md`](../../../../../concept/03_advanced/01_concurrency.md) | 🔬 分离逻辑、死锁分析 |

### Ch.17: 异步编程基础（第三版新增 ⭐）

| TRPL § | 主题 | 本项目对应 | 补充深度 |
|:---|:---|:---|:---:|
| **17.1 Futures and the Async Syntax** | `async fn`、`.await`、`Future` trait | [`concept/03_advanced/02_async.md`](../../../../../concept/03_advanced/02_async.md) §一/§三 | 🔬 状态机精确推导 |
| **17.2 Applying Concurrency with Async** | 并发 vs 异步、Tokio | [`crates/c06_async/docs/tier_02_guides/`](../../../../../crates/c06_async/docs/tier_02_guides) | 📦 运行时选择指南 |
| **17.3 Working With Any Number of Futures** | `join!`、`select!` | [`crates/c06_async/docs/README.md`](../../../../../crates/c06_async/docs/README.md) §5 | 📦 `tokio::join!` 示例 |
| **17.4 Streams: Futures in Sequence** | `Stream` trait、异步迭代 | [`concept/03_advanced/02_async.md`](../../../../../concept/03_advanced/02_async.md) §十五 | 🔬 Stream/Dataflow 映射 |
| **17.5 A Closer Look at the Traits for Async** | `Future`、`Stream`、`Sink` | [`concept/03_advanced/02_async.md`](../../../../../concept/03_advanced/02_async.md) §8.10 | 🔬 Pin LTL 形式化 |
| **17.6 Futures, Tasks, and Threads** | 任务调度、线程池对比 | [`concept/03_advanced/02_async.md`](../../../../../concept/03_advanced/02_async.md) §2.1/§3.5 | 🔬 执行模型同构性矩阵 |

### Ch.18-22: 高级特性与附录

| TRPL 章节 | 主题 | 本项目对应 | 补充深度 |
|:---|:---|:---|:---:|
| Ch.18 OOP 特性 | trait 对象、动态分发 | [`concept/02_intermediate/01_traits.md`](../../../../../concept/02_intermediate/01_traits.md) §对象安全 | 🔬 存在类型形式化 |
| Ch.19 模式与匹配 | 穷尽性、守卫、`@` 绑定 | [`concept/02_intermediate/05_assert_matches.md`](../../../../../concept/02_intermediate/05_assert_matches.md) | 🔬 模式匹配形式化 |
| Ch.20 高级特性 | unsafe、trait 别名、关联类型 | [`concept/03_advanced/03_unsafe.md`](../../../../../concept/03_advanced/03_unsafe.md) | 🔬 Miri、FFI、repr |
| Ch.21 多线程 Web 服务器 | 综合项目 | [`crates/c10_networks/`](../../../../../crates/c10_networks) | 📦 完整网络 crate |
| Ch.22 附录 | 关键字、运算符、派生宏 | [`docs/02_reference/`](../../docs/02_reference) | 📚 速查表集合 |

---

## 第三版 vs 第二版 关键差异

| 变化 | 说明 | 本项目覆盖 |
|:---|:---|:---:|
| **新增 Ch.17 异步编程** | 6 节完整异步基础 | ✅ 全映射 |
| **`gen` 关键字预留** | 为生成器做准备 | ✅ `concept/07_future/03_evolution.md` |
| **异步闭包 `async \| \| {}`** | Edition 2024 特性 | ✅ `docs/03_guides/rust_2024_edition_migration_guide.md` |
| **`unsafe` 块新规则** | 嵌套 unsafe 需显式标记 | ✅ 迁移指南 §4.1 |
| **`std::env::set_var` unsafe** | 环境变量操作需 unsafe | ✅ 迁移指南 §4.2 |
| **Miri 内容** | TRPL 新增 Miri 介绍 | ✅ `concept/03_advanced/03_unsafe.md` §Miri |

---

## 学习路径建议

### 路径 A：按 TRPL 顺序 + 本项目深化

```text
TRPL Ch.1-6  →  本项目 L1 基础概念（所有权、类型系统）
     ↓
TRPL Ch.7-10 →  本项目 L2 进阶（泛型、Trait、生命周期）
     ↓
TRPL Ch.11-16 → 本项目 L3 高级（并发、智能指针）
     ↓
TRPL Ch.17   →  本项目 L3 异步（形式化语义 + 实践指南）
     ↓
TRPL Ch.18-22 → 本项目 L4 形式化 + L6 生态
```

### 路径 B：按本项目分层 + TRPL 对照

```text
本项目 L1 → 对照 TRPL Ch.3-6（基础验证）
本项目 L2 → 对照 TRPL Ch.8-10（进阶验证）
本项目 L3 → 对照 TRPL Ch.15-17（高级应用）
本项目 L4 → 延伸阅读 TRPL 附录 + 形式化论文
```

---

**文档版本**: 1.0
**对应 TRPL 版本**: 第三版 (2024 Edition) / Rust 1.85.0+
**最后更新**: 2026-06-01
**状态**: ✅ 索引创建完成

> **权威来源**: [The Rust Programming Language 第三版](https://doc.rust-lang.org/book/), [NoStarch 印刷版](https://nostarch.com/rust-programming-language-3e)
