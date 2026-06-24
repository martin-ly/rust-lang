//! Kani 函数合约 / 循环合约示例
//!
//! 本模块展示如何用 `#[kani::requires]`、`#[kani::ensures]` 与
//! `#[kani::loop_invariant]` 对所有权、借用和循环进行形式化验证。
//! 这些示例仅在 `cargo kani` 运行时编译，常规 `cargo build/test` 会跳过。

/// 示例 1：函数合约 —— 严格递增函数
#[cfg(kani)]
#[kani::requires(x > 0)]
#[kani::ensures(|result| *result > x)]
fn increment(x: u32) -> u32 {
    x + 1
}

/// 验证 `increment` 的函数合约
#[cfg(kani)]
#[kani::proof]
fn verify_increment_contract() {
    let x: u32 = kani::any();
    let _ = increment(x);
}

/// 示例 2：循环合约 —— 非负数数组求和
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

/// 示例 3：函数合约 + 循环合约 —— 非空切片最大值
#[cfg(kani)]
#[kani::requires(!s.is_empty())]
#[kani::ensures(|result| s.iter().all(|x| *result >= *x))]
#[kani::ensures(|result| s.iter().any(|x| *result == *x))]
fn max_in_slice(s: &[i32]) -> i32 {
    let mut max = s[0];
    #[kani::loop_invariant(
        max == s[0] || s.iter().any(|x| *x == max)
    )]
    for &x in s {
        if x > max {
            max = x;
        }
    }
    max
}

/// 验证 `max_in_slice` 的函数合约
#[cfg(kani)]
#[kani::proof]
fn verify_max_in_slice_contract() {
    let s: [i32; 4] = [kani::any(), kani::any(), kani::any(), kani::any()];
    let _ = max_in_slice(&s);
}
