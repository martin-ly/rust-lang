//! L1 基础概念可运行测验
//!
//! 覆盖所有权、借用、生命周期核心概念
//! 运行: cargo test -p exercises --test l1_foundation

// ============================================================================
// 测验 1: Move vs Copy
// ============================================================================

#[test]
fn test_copy_semantics() {
    let a = 5i32;
    let b = a;
    // i32 实现 Copy，赋值后 a 仍可用
    assert_eq!(a, 5);
    assert_eq!(b, 5);
}

#[test]
fn test_move_semantics() {
    let s1 = String::from("hello");
    let s2 = s1;
    // s1 的所有权已 move 到 s2
    assert_eq!(s2, "hello");
    // 若使用 s1 会编译错误: use of moved value
}

#[test]
fn test_clone_vs_move() {
    let s1 = String::from("world");
    let s2 = s1.clone();
    // clone 后 s1 仍可用
    assert_eq!(s1, "world");
    assert_eq!(s2, "world");
}

// ============================================================================
// 测验 2: 所有权转移规则
// ============================================================================

fn take_ownership(s: String) -> usize {
    s.len()
}

#[test]
fn test_ownership_transfer_to_function() {
    let s = String::from("hello");
    let len = take_ownership(s);
    // s 已 move 进函数，此处不可再用
    assert_eq!(len, 5);
}

#[test]
fn test_borrow_instead_of_move() {
    let s = String::from("hello");
    let len = borrow_string(&s);
    // s 仍可用，因为只是借用
    assert_eq!(len, 5);
    assert_eq!(s, "hello");
}

fn borrow_string(s: &String) -> usize {
    s.len()
}

// ============================================================================
// 测验 3: Drop 语义（LIFO）
// ============================================================================

use std::sync::atomic::{AtomicUsize, Ordering};

static DROP_ORDER: AtomicUsize = AtomicUsize::new(0);

struct DropRecorder(&'static str, usize);

impl Drop for DropRecorder {
    fn drop(&mut self) {
        let order = DROP_ORDER.fetch_add(1, Ordering::SeqCst);
        assert_eq!(order, self.1, "{} dropped out of order", self.0);
    }
}

#[test]
fn test_drop_lifo_order() {
    DROP_ORDER.store(0, Ordering::SeqCst);
    {
        let _b = DropRecorder("b", 0);
        // b 在作用域结束时先 drop
    }
    let _a = DropRecorder("a", 1);
    // a 在函数结束时后 drop
}

// ============================================================================
// 测验 4: 借用规则基础
// ============================================================================

#[test]
fn test_multiple_immutable_borrows() {
    let x = 5;
    let r1 = &x;
    let r2 = &x;
    let r3 = &x;
    // 多个不可变借用可以共存
    assert_eq!(*r1 + *r2 + *r3, 15);
}

#[test]
fn test_mutable_borrow_exclusivity() {
    let mut x = 5;
    let r = &mut x;
    *r += 1;
    // 可变借用期间，不能有其他借用
    assert_eq!(*r, 6);
}

#[test]
fn test_reborrow_safety() {
    let mut s = String::from("hello");
    let r1 = &mut s;
    let r2 = &mut *r1;
    r2.push_str(" world");
    // reborrow 结束后 r1 恢复可用
    assert_eq!(*r1, "hello world");
}

// ============================================================================
// 测验 5: Two-Phase Borrow
// ============================================================================

#[test]
fn test_two_phase_borrow_vec_push() {
    let mut v = vec![1, 2, 3];
    // Two-Phase Borrow: v.len() 不可变借用与 v.push() 可变借用短暂共存
    v.push(v.len() as i32);
    assert_eq!(v, vec![1, 2, 3, 3]);
}

// ============================================================================
// 测验 6: Split Borrow
// ============================================================================

#[test]
fn test_split_borrow_disjoint_fields() {
    struct Point {
        x: i32,
        y: i32,
    }
    let mut p = Point { x: 0, y: 0 };
    let x = &mut p.x;
    let y = &mut p.y;
    *x += 1;
    *y += 2;
    assert_eq!(p.x, 1);
    assert_eq!(p.y, 2);
}

// ============================================================================
// 测验 7: 生命周期省略规则
// ============================================================================

#[test]
fn test_lifetime_elision() {
    fn first_word(s: &str) -> &str {
        s.split_whitespace().next().unwrap_or(s)
    }
    let s = "hello world";
    let word = first_word(s);
    assert_eq!(word, "hello");
}

// ============================================================================
// 测验 8: 悬垂引用防护
// ============================================================================

#[test]
fn test_no_dangling_reference() {
    // 以下代码若写成函数返回 &String 会编译失败
    // Rust 编译器阻止悬垂引用
    fn make_string() -> String {
        String::from("safe")
    }
    let s = make_string();
    assert_eq!(s, "safe");
}

// ============================================================================
// 测验 9: NLL (Non-Lexical Lifetimes)
// ============================================================================

#[test]
fn test_nll_allows_early_drop() {
    let mut x = String::from("hello");
    let y = &x;
    println!("{}", y); // y 最后一次使用
    // NLL: y 的借用在此处结束
    let z = &mut x;
    z.push_str(" world");
    assert_eq!(x, "hello world");
}

// ============================================================================
// 测验 10: 集合所有权
// ============================================================================

#[test]
fn test_vec_ownership() {
    let mut v = vec![1, 2, 3];
    v.push(4);
    assert_eq!(v.len(), 4);
    // Vec 拥有其元素的所有权
}

#[test]
fn test_string_ownership() {
    let mut s = String::from("hello");
    s.push_str(", world");
    assert_eq!(s, "hello, world");
}

// ============================================================================
// 测验 11: 数值溢出与 wrapping
// ============================================================================

#[test]
fn test_integer_wrapping() {
    let x: u8 = 255;
    let y = x.wrapping_add(1);
    let z = x.saturating_add(1);
    assert_eq!(y, 0); // wrapping: 255 + 1 = 0
    assert_eq!(z, 255); // saturating: 255 + 1 = 255 (clamp)
}

// ============================================================================
// 测验 12: `as` 截断转换
// ============================================================================

#[test]
fn test_as_cast_truncation() {
    let a: i32 = -1;
    let b = a as u32;
    assert_eq!(b, u32::MAX); // -1 的 two's complement 重新解释

    let c: i32 = 300;
    let d = c as i8;
    assert_eq!(d, 44); // 300 的低 8 位 = 44
}

// ============================================================================
// 测验 13: NaN 比较行为
// ============================================================================

#[test]
fn test_nan_not_equal() {
    let x: f64 = f64::NAN;
    assert!(!(x == f64::NAN)); // NaN != NaN
    assert!(x.is_nan()); // 必须使用 is_nan() 检测
}

// ============================================================================
// 测验 14: loop 返回值
// ============================================================================

#[test]
fn test_loop_returns_value() {
    let mut count = 0;
    let result = loop {
        count += 1;
        if count == 3 {
            break count * 2;
        }
    };
    assert_eq!(result, 6);
}

// ============================================================================
// 测验 15: Vec 容量与 with_capacity
// ============================================================================

#[test]
fn test_vec_with_capacity() {
    let mut v = Vec::with_capacity(10);
    v.push(1);
    v.push(2);
    assert_eq!(v.len(), 2);
    assert_eq!(v.capacity(), 10);
}

// ============================================================================
// 测验 16: String 自动解引用为 &str
// ============================================================================

#[test]
fn test_string_deref_to_str() {
    fn greet(name: &str) -> String {
        format!("Hello, {name}!")
    }
    let s = String::from("Alice");
    assert_eq!(greet(&s), "Hello, Alice!");
    assert_eq!(greet("Bob"), "Hello, Bob!");
}
