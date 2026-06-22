//! Kani 0.66+ 验证示例
//!
//! 本模块包含使用 Kani 0.66 新特性（quantifiers、loop contracts）的示例。
//! 这些示例仅在 `cargo kani` 运行时编译，常规 `cargo build/test` 会跳过。

/// 证明：所有元素非负时，数组和也非负
#[cfg(kani)]
#[kani::proof]
fn sum_of_nonnegative_array_is_nonnegative() {
    let arr: [i32; 4] = [kani::any(), kani::any(), kani::any(), kani::any()];
    kani::assume(kani::forall!(|i in 0..4| arr[i] >= 0));

    let mut sum = 0i64;
    #[kani::loop_invariant(sum >= 0)]
    for &x in &arr {
        sum += x as i64;
    }

    assert!(sum >= 0);
}

/// 证明：二分查找前置条件满足时返回正确索引
#[cfg(kani)]
#[kani::proof]
fn binary_search_finds_target() {
    let arr = [1, 3, 5, 7, 9];
    let target: i32 = kani::any();
    kani::assume(kani::exists!(|i in 0..arr.len()| arr[i] == target));

    let result = crate::topics::searching::SearchingEngine::binary_search_sync(&arr, &target);
    assert!(result.is_some());
    let idx = result.unwrap();
    assert!(arr[idx] == target);
}
