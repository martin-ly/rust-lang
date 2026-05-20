//! `derive(CoercePointee)` 跟踪模块
//!
//! **Rust 版本**: nightly 实验性
//! **RFC**: 尚未正式发布（设计讨论阶段）
//! **相关特性**: Arbitrary Self Types v2, Field Projections, Smart Pointer ergonomics
//!
//! **来源**: [Rust Project Goals 2026 — Beyond the &] · [Arbitrary Self Types v2 跟踪]
//!
//! # 概念定义
//!
//! `CoercePointee` 是 Rust 智能指针生态中缺失的关键拼图：
//! 它允许编译器**自动将 `&T` 强制转换为 `SmartPtr<T>`**（当 `SmartPtr<T>` 实现了 `Deref<Target=T>` 时）。
//!
//! ```text
//! 当前 Rust:                    启用 CoercePointee 后:
//! ────────────                  ──────────────────────
//! let rc = Rc::new(5);         let rc: Rc<i32> = &5;  // 自动强制转换
//!                              // 或
//!                              fn foo(x: Rc<i32>) {}
//!                              foo(&5);  // &i32 → Rc<i32>
//! ```
//!
//! # 为什么需要 CoercePointee？
//!
//! | 问题 | 当前 workaround | CoercePointee 解决 |
//! |:---|:---|:---|
//! | `Arc<str>` 从 `&str` 构造 | `Arc::from("hello")` | `let s: Arc<str> = "hello";` |
//! | `Box<dyn Trait>` 从具体类型 | `Box::new(x) as Box<dyn Trait>` | `let b: Box<dyn Trait> = &x;` |
//! | `Rc<Path>` 从 `&Path` | `Rc::from(path)` | 自动强制 |
//!
//! # 设计状态（2026-05）
//!
//! | 里程碑 | 状态 | 预计 |
//! |:---|:---:|:---:|
//! | 设计讨论 | 🟡 活跃 | — |
//! | RFC 提交 | 🔴 待完成 | 2026 H2 |
//! | 原型实现 | 🔴 无 | — |
//! | 稳定化 | 🔴 远期 | 2027+ |
//!
//! # 与 Field Projections 的关系
//!
//! ```text
//! Beyond the & 旗舰主题的两个支柱:
//! ┌─────────────────────────┬─────────────────────────┐
//! │   Field Projections     │   derive(CoercePointee) │
//! │   (智能指针访问字段)     │   (自动强制转换)        │
//! ├─────────────────────────┼─────────────────────────┤
//! │  rc.field 代替 (*rc).field│  SmartPtr<T> 从 &T 自动构造│
//! │  Pin 投影已稳定          │  仍在设计中              │
//! └─────────────────────────┴─────────────────────────┘
//! ```
//!
//! # 参考
//!
//! - [Rust Project Goals: Beyond the &](https://rust-lang.github.io/rust-project-goals/2026/flagships.html)
//! - [Arbitrary Self Types v2 设计文档]
//!
//! ---
//!
//! > **文档版本**: 1.0
//! > **最后更新**: 2026-05-21
//! > **状态**: 🟡 跟踪观察

/// 标记本模块为跟踪性质，无稳定代码
#[cfg(doc)]
mod design_notes {
    //! # 设计笔记
    //!
    //! ## 可能的 `derive(CoercePointee)` 实现方向
    //!
    //! ```rust,ignore
    //! // 方案 A: 自动推导 (类似 Deref)
    //! #[derive(CoercePointee)]
    //! struct MySmartPtr<T: ?Sized> {
    //!     ptr: *mut T,
    //! }
    //!
    //! // 方案 B: 显式标注源类型
    //! #[derive(CoercePointee)]
    //! #[coerce_from(&T)]
    //! struct MySmartPtr<T: ?Sized> {
    //!     ptr: *mut T,
    //! }
    //! ```
}

#[cfg(not(doc))]
pub const TRACKING_STATUS: &str = "RFC 前设计阶段";

#[cfg(not(doc))]
pub const ESTIMATED_RFC: &str = "2026 H2";

#[cfg(not(doc))]
pub const RELATED_FEATURES: &[&str] = &[
    "Arbitrary Self Types v2",
    "Field Projections",
    "Beyond the & (旗舰主题)",
];
