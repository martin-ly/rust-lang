//! # Brown University CRP Ownership Inventory 练习
//!
//! **EN**: Brown University CRP Ownership Inventory Module
//! **Summary**: Module containing 8 exercises inspired by the Brown University CRP Ownership
//! Inventory, covering core Rust ownership subtopics.
//! **Key Terms**: 所有权 (ownership), 借用 (borrowing), 生命周期 (lifetime), RAII,
//! 移动语义 (move semantics), Copy 语义 (copy semantics), 可变借用 (mutable borrow).
//! **Related Concepts**:
//! [`concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md),
//! [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md),
//! [`concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md),
//! [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md).
//!
//! 本模块包含 8 个基于 Brown University CRP Ownership Inventory 模式编写的练习，
//! 覆盖 Rust 所有权系统的核心子主题：
//!
//! This module contains 8 exercises inspired by the Brown University CRP Ownership Inventory,
//! covering core ownership subtopics:
//!
//! - 移动语义 vs. Copy 语义 / Move vs. Copy semantics
//! - 可变借用规则 / Mutable borrowing rules
//! - 悬垂引用 / Dangling references
//! - 生命周期标注 / Lifetime annotations
//! - RAII 与 Drop 语义 / RAII and Drop semantics
//! - 借用检查器错误修复 / Fixing borrow checker errors
//! - Vec 重新分配与切片失效 / Vec reallocation and slice invalidation
//! - 循环中的所有权 / Ownership in loops

pub mod inventory_01;
pub mod inventory_02;
pub mod inventory_03;
pub mod inventory_04;
pub mod inventory_05;
pub mod inventory_06;
pub mod inventory_07;
pub mod inventory_08;
