//! Kani 函数合约 / 循环合约示例（控制流与函数）
//!
//! 本模块展示如何用 `#[kani::requires]`、`#[kani::ensures]` 与
//! `#[kani::loop_invariant]` 对控制流、函数和循环进行形式化验证。
//! 这些示例仅在 `cargo kani` 运行时编译，常规 `cargo build/test` 会跳过。

/// 示例 1：函数合约 —— 两数最大值
///
/// 后置条件：返回值同时不小于 `a` 与 `b`，且一定等于 `a` 或 `b` 其中之一。
#[cfg(kani)]
#[kani::ensures(|result| *result >= a && *result >= b)]
#[kani::ensures(|result| *result == a || *result == b)]
fn max_of_two(a: i32, b: i32) -> i32 {
    if a >= b {
        a
    } else {
        b
    }
}

/// 验证 `max_of_two` 的函数合约
#[cfg(kani)]
#[kani::proof]
fn verify_max_of_two_contract() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();
    let _ = max_of_two(a, b);
}

/// 示例 2：循环合约 —— 统计非负偶数个数
///
/// 通过 `kani::assume` 限制输入非负，再用循环不变量证明计数结果符合预期。
#[cfg(kani)]
#[kani::proof]
fn count_even_nonnegative_is_exact() {
    let arr: [i32; 4] = [kani::any(), kani::any(), kani::any(), kani::any()];
    kani::assume(kani::forall!(|i in 0..4| arr[i] >= 0));

    let mut count = 0usize;
    #[kani::loop_invariant(
        count == arr.iter().take(i).filter(|&&x| x % 2 == 0).count()
    )]
    for (i, &x) in arr.iter().enumerate() {
        if x % 2 == 0 {
            count += 1;
        }
    }

    assert!(count <= 4);
    assert_eq!(count, arr.iter().filter(|&&x| x % 2 == 0).count());
}

/// 示例 3：函数合约 —— 带前置条件的整数除法
///
/// 前置条件：`divisor` 不能为零，避免 panic。
/// 后置条件：若被除数与除数同号则商非负，异号则商非正。
#[cfg(kani)]
#[kani::requires(divisor != 0)]
#[kani::ensures(|result| (*result == 0) || ((*result > 0) == ((dividend > 0) == (divisor > 0))))]
fn checked_div_relation(dividend: i32, divisor: i32) -> i32 {
    dividend / divisor
}

/// 验证 `checked_div_relation` 的函数合约
#[cfg(kani)]
#[kani::proof]
fn verify_checked_div_relation_contract() {
    let dividend: i32 = kani::any();
    let divisor: i32 = kani::any();
    let _ = checked_div_relation(dividend, divisor);
}

/// 示例 4：循环不变量 —— 带下标边界的线性搜索
///
/// 使用 `#[kani::loop_invariant]` 证明下标 `i` 始终不越界，
/// 且当找到目标时返回的索引合法。
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn verify_linear_search_index_in_bounds() {
    let arr: [u8; 4] = [kani::any(), kani::any(), kani::any(), kani::any()];
    let target: u8 = kani::any();
    let mut result: Option<usize> = None;

    let mut i = 0usize;
    #[kani::loop_invariant(i <= arr.len())]
    #[kani::loop_invariant(result.is_none() || result.unwrap() < arr.len())]
    while i < arr.len() {
        if arr[i] == target {
            result = Some(i);
            break;
        }
        i += 1;
    }

    assert!(i <= arr.len());
    assert!(result.is_none() || result.unwrap() < arr.len());
}
