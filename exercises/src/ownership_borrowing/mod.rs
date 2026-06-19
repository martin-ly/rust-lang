//! # 所有权与借用练习 / Ownership and Borrowing Exercises
//!
//! 本模块包含练习题，涵盖：
//! This module contains exercises covering:
//! - 借用检查器规则 / Borrow checker rules
//! - 字符串 slice 与所有权 / String slices and ownership
//! - 可变引用规则 / Mutable reference rules
//! - 生命周期标注 / Lifetime annotations
//! - 智能指针共享所有权 / Smart pointers for shared ownership
//! - Brown Book Ownership Inventory 样题 / Brown Book Ownership Inventory sample exercises
//! - 字符串替换链 / String replacement chain
//! - Vec 与切片借用冲突 / Vec and slice borrow conflicts
//! - 避免悬垂引用 / Avoiding dangling references
//! - 悬垂栈引用 / Dangling stack references
//! - Vec 重新分配 / Vec reallocation
//! - HashMap 借用冲突 / HashMap borrow conflicts
//! - 循环中的所有权 / Ownership in loops

pub mod ex01_borrow_checker_fix;
pub mod ex02_string_slice;
pub mod ex03_mutable_borrow;
pub mod ex04_lifetime_basic;
pub mod ex05_smart_pointer_rc;
pub mod ex06_string_replace_chain;
pub mod ex07_vec_slice_borrow;
pub mod ex08_dangling_reference;
pub mod ex09_dangling_stack_reference;
pub mod ex10_vec_reallocation;
pub mod ex11_hashmap_borrow;
pub mod ex12_string_in_loop;
