//! **Rust 版本**: nightly 实验性
//! **Rust 版this**: nightly 实验性
//! **RFC**: 尚未正式发布（设计讨论阶段）
//! **RFC**: （design stage ）
//! **相关特性**: Arbitrary Self Types v2, Field Projections, Smart Pointer ergonomics
//! **相关feature**: Arbitrary Self Types v2, Field Projections, Smart Pointer ergonomics
//! **来源**: [Rust Project Goals 2026 — Beyond the &] · [Arbitrary Self Types v2 跟踪]
//! **source**: [Rust Project Goals 2026 — Beyond the &] · [Arbitrary Self Types v2 跟踪]
//! # 概念定义
//! # concept definition
//! let rc = Rc::new(5);         let rc: Rc<i32> = &5;  // 自动强制转换
//! let rc = Rc::new(5); let rc: Rc<i32> = &5; // 自动强制conversion
//!                              // 或
//!                              // or
//!                              foo(&5);  // &i32 → Rc<i32>
//! ```
//!
//! | `Arc<str>` 从 `&str` 构造 | `Arc::from("hello")` | `let s: Arc<str> = "hello";` |
//! | `Arc<str>` from `&str` 构造 | `Arc::from("hello")` | `let s: Arc<str> = "hello";` |
//! | `Box<dyn Trait>` 从具体类型 | `Box::new(x) as Box<dyn Trait>` | `let b: Box<dyn Trait> = &x;` |
//! | `Rc<Path>` 从 `&Path` | `Rc::from(path)` | 自动强制 |
//! | `Rc<Path>` from `&Path` | `Rc::from(path)` | 自动强制 |
//! # 设计状态（2026-05）
//! # design state （2026-05）
//! | 里程碑 | 状态 | 预计 |
//! | | state | |
//! | 设计讨论 | 🟡 活跃 | — |
//! | design | 🟡 | — |
//! | RFC 提交 | 🔴 待完成 | 2026 H2 |
//! | RFC | 🔴 | 2026 H2 |
//! | 原型实现 | 🔴 无 | — |
//! | | 🔴 | — |
//! | 原型Implementation of | 🔴 无 | — |
//! | 稳定化 | 🔴 远期 | 2027+ |
//! | | 🔴 far-term | 2027+ |
//! | 稳定化 | 🔴 far-term | 2027+ |
//! # and Field Projections 关系
//! │   (智能指针访问字段)     │   (自动强制转换)        │
//! │ (pointer field ) │ (conversion ) │
//! │  Pin 投影已稳定          │  仍在设计中              │
//! │ Pin │ in design in │
//! │ Pin 投影已稳定 │ 仍indesignin │
//!
//! # 参考
//! # reference
//! - [Rust Project Goals: Beyond the &](https://rust-lang.github.io/rust-project-goals/2026/flagships.html)
//! - [Arbitrary Self Types v2 设计文档]
//!
//! > **文档版本**: 1.0
//! > **this **: 1.0
//! > **文档版this**: 1.0
//! > **this**: 1.0
//! > **最后更新**: 2026-05-21
//! > **finally **: 2026-05-21
//! > **状态**: 🟡 跟踪观察
//! > **state **: 🟡
//! > **state**: 🟡 跟踪观察
//! > **state**: 🟡

/// 标记本模块为跟踪性质，无稳定代码
/// mark this module as ，
#[cfg(doc)]
mod design_notes {
    //! # 设计笔记
    //! # design
    //! ```rust,ignore
    //! // 方案 A: 自动推导 (类似 Deref)
    //! // A: (similar to Deref)
    //! // 方案 A: 自动推导 (similar to Deref)
    //!     ptr: *mut T,
    //! }
    //!
    //! // 方案 B: 显式标注源类型
    //! // B: type
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
