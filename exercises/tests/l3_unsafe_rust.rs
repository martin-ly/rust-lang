//! L3 Unsafe Rust 集成测试 / Integration tests for the unsafe_rust module
//!
//! 运行: cargo test -p exercises --test l3_unsafe_rust

use exercises::unsafe_rust::*;
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicUsize, Ordering};

#[test]
fn test_read_and_double_basic() {
    let mut value = 21;
    let old = read_and_double(&mut value);
    assert_eq!(old, 21);
    assert_eq!(value, 42);
}

#[test]
fn test_read_and_double_negative() {
    let mut value = -5;
    let old = read_and_double(&mut value);
    assert_eq!(old, -5);
    assert_eq!(value, -10);
}

#[test]
fn test_increment_raw_pointer() {
    let mut value = 100;
    // SAFETY: `&mut value` 保证指针有效且对齐。
    // SAFETY: `&mut value` guarantees a valid, aligned pointer.
    let new = unsafe { increment_raw_pointer(&mut value) };
    assert_eq!(value, 101);
    assert_eq!(new, 101);
}

#[test]
fn test_clone_via_raw_parts_empty() {
    let empty: &[i32] = &[];
    let cloned = clone_via_raw_parts(empty);
    assert!(cloned.is_empty());
}

#[test]
fn test_clone_via_raw_parts_integers() {
    let data = [1, 2, 3, 4, 5];
    let cloned = clone_via_raw_parts(&data);
    assert_eq!(cloned, vec![1, 2, 3, 4, 5]);
}

#[test]
fn test_zero_prefix_basic() {
    let mut bytes = [1, 2, 3, 4, 5];
    zero_prefix(&mut bytes, 2);
    assert_eq!(bytes, [0, 0, 3, 4, 5]);
}

#[test]
fn test_zero_prefix_zero() {
    let mut bytes = [1, 2, 3];
    zero_prefix(&mut bytes, 0);
    assert_eq!(bytes, [1, 2, 3]);
}

#[test]
fn test_zero_prefix_full() {
    let mut bytes = [9, 8, 7];
    zero_prefix(&mut bytes, 3);
    assert_eq!(bytes, [0, 0, 0]);
}

#[test]
#[should_panic(expected = "n 超出切片长度")]
fn test_zero_prefix_out_of_bounds() {
    let mut bytes = [1, 2];
    zero_prefix(&mut bytes, 3);
}

#[test]
fn test_init_array_from_fn() {
    let arr = init_array_from_fn::<i32, 5>(|i| i as i32 * 2);
    assert_eq!(arr, [0, 2, 4, 6, 8]);
}

#[test]
fn test_init_array_from_fn_drop_safety() {
    static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

    struct DropCounter;
    impl Drop for DropCounter {
        fn drop(&mut self) {
            DROP_COUNT.fetch_add(1, Ordering::SeqCst);
        }
    }

    DROP_COUNT.store(0, Ordering::SeqCst);

    let result = std::panic::catch_unwind(|| {
        let mut count = 0;
        let _ = init_array_from_fn::<DropCounter, 5>(|_| {
            count += 1;
            if count == 4 {
                panic!("boom");
            }
            DropCounter
        });
    });

    assert!(result.is_err());
    // 前 3 个已初始化的 DropCounter 在 panic 时被正确 drop。
    // The first 3 initialized DropCounters are dropped correctly on panic.
    assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 3);
}

#[test]
fn test_increment_shared_counter() {
    let counter = UnsafeCell::new(0);
    assert_eq!(increment_shared_counter(&counter), 1);
    assert_eq!(increment_shared_counter(&counter), 2);
    assert_eq!(increment_shared_counter(&counter), 3);
    assert_eq!(unsafe { *counter.get() }, 3);
}

#[test]
fn test_call_ffi_add_one() {
    assert_eq!(call_ffi_add_one(0), 1);
    assert_eq!(call_ffi_add_one(41), 42);
    assert_eq!(call_ffi_add_one(-10), -9);
}

#[test]
fn test_safe_split_at_mut_basic() {
    let mut arr = [1, 2, 3, 4, 5];
    let (left, right) = safe_split_at_mut(&mut arr, 2);
    assert_eq!(left, &[1, 2]);
    assert_eq!(right, &[3, 4, 5]);
}

#[test]
fn test_safe_split_at_mut_mutability() {
    let mut arr = [10, 20, 30, 40];
    let (left, right) = safe_split_at_mut(&mut arr, 2);
    left[0] = 99;
    right[1] = 88;
    assert_eq!(arr, [99, 20, 30, 88]);
}

#[test]
fn test_safe_split_at_mut_boundaries() {
    let mut arr = [1, 2, 3];
    let (left, right) = safe_split_at_mut(&mut arr, 0);
    assert_eq!(left, &[]);
    assert_eq!(right, &[1, 2, 3]);

    let mut arr2 = [4, 5, 6];
    let (left, right) = safe_split_at_mut(&mut arr2, 3);
    assert_eq!(left, &[4, 5, 6]);
    assert_eq!(right, &[]);
}

#[test]
#[should_panic(expected = "mid 索引越界")]
fn test_safe_split_at_mut_panic_on_oob() {
    let mut arr = [1, 2, 3];
    let _ = safe_split_at_mut(&mut arr, 4);
}
