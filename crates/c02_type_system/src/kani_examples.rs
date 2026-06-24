//! Kani 类型系统函数合约 / 循环合约示例
//!
//! 本模块展示如何用 `#[kani::requires]`、`#[kani::ensures]` 与
//! `#[kani::loop_invariant]` 对泛型、trait 和类型约束进行形式化验证。
//! 这些示例仅在 `cargo kani` 运行时编译，常规 `cargo build/test` 会跳过。

/// 示例 1：泛型函数合约 —— 恒等函数
#[cfg(kani)]
#[kani::ensures(|result| *result == x)]
fn identity<T>(x: T) -> T
where
    T: Copy + PartialEq,
{
    x
}

/// 验证 `identity` 的函数合约
#[cfg(kani)]
#[kani::proof]
fn verify_identity_contract() {
    let x: u32 = kani::any();
    assert_eq!(identity(x), x);
}

/// 示例 2：trait bound 函数合约 —— 求和
#[cfg(kani)]
#[kani::requires(!values.is_empty())]
#[kani::ensures(|result| values.iter().all(|v| *result >= *v))]
#[kani::ensures(|result| values.iter().any(|v| *result == *v))]
fn max_of_slice(values: &[i32]) -> i32 {
    let mut max = values[0];
    #[kani::loop_invariant(
        max == values[0] || values.iter().any(|v| *v == max)
    )]
    for &v in values {
        if v > max {
            max = v;
        }
    }
    max
}

/// 验证 `max_of_slice` 的函数合约
#[cfg(kani)]
#[kani::proof]
fn verify_max_of_slice_contract() {
    let values: [i32; 4] = [kani::any(), kani::any(), kani::any(), kani::any()];
    let _ = max_of_slice(&values);
}

/// 示例 3：循环合约 —— 统计偶数个数
#[cfg(kani)]
#[kani::proof]
fn verify_count_even() {
    let arr: [i32; 4] = [kani::any(), kani::any(), kani::any(), kani::any()];

    let mut count = 0usize;
    #[kani::loop_invariant(
        count == arr.iter().take(i).filter(|&&x| x % 2 == 0).count()
    )]
    for (i, &x) in arr.iter().enumerate() {
        if x % 2 == 0 {
            count += 1;
        }
    }

    assert_eq!(count, arr.iter().filter(|&&x| x % 2 == 0).count());
}
