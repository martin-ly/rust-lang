//! Kani 泛型函数合约 / 泛型循环合约示例
//!
//! 本模块展示如何用 `#[kani::requires]`、`#[kani::ensures]` 与
//! `#[kani::loop_invariant]` 对泛型函数与泛型循环数据进行形式化验证。
//! 这些示例仅在 `cargo kani` 运行时编译，常规 `cargo build/test` 会跳过。

/// 示例 1：泛型函数合约 —— 在切片中查找目标元素的下标
///
/// 后置条件保证：
/// - 若返回 `Some(i)`，则 `slice[i] == target`；
/// - 若返回 `None`，则切片中不存在等于 `target` 的元素。
#[cfg(kani)]
#[kani::ensures(|result| if let Some(idx) = *result { idx < slice.len() && slice[idx] == target } else { true })]
#[kani::ensures(|result| *result != None || !slice.iter().any(|x| *x == target))]
fn find_index<T>(slice: &[T], target: T) -> Option<usize>
where
    T: PartialEq + Copy,
{
    for (i, &x) in slice.iter().enumerate() {
        if x == target {
            return Some(i);
        }
    }
    None
}

/// 验证 `find_index` 的泛型函数合约
#[cfg(kani)]
#[kani::proof]
fn verify_find_index_contract() {
    let slice: [u32; 4] = [kani::any(), kani::any(), kani::any(), kani::any()];
    let target: u32 = kani::any();
    let _ = find_index(&slice, target);
}

/// 示例 2：泛型循环合约 —— 统计目标元素在切片中的出现次数
///
/// 使用循环不变量将部分遍历的计数结果与 `Iterator` 语义对应起来。
#[cfg(kani)]
#[kani::proof]
fn verify_count_occurrences_generic() {
    let slice: [u32; 4] = [kani::any(), kani::any(), kani::any(), kani::any()];
    let target: u32 = kani::any();

    let mut count = 0usize;
    #[kani::loop_invariant(
        count == slice.iter().take(i).filter(|&&x| x == target).count()
    )]
    for (i, &x) in slice.iter().enumerate() {
        if x == target {
            count += 1;
        }
    }

    assert_eq!(count, slice.iter().filter(|&&x| x == target).count());
}

/// 示例 3：泛型函数合约 —— 将值限制在闭区间 `[low, high]` 内
///
/// 要求 `T` 支持全序比较；前置条件保证 `low <= high`。
/// 后置条件保证返回值落在闭区间 `[low, high]` 内。
#[cfg(kani)]
#[kani::requires(low <= high)]
#[kani::ensures(|result| *result >= low && *result <= high)]
fn clamp<T>(value: T, low: T, high: T) -> T
where
    T: Ord,
{
    if value < low {
        low
    } else if value > high {
        high
    } else {
        value
    }
}

/// 验证 `clamp` 的泛型函数合约
#[cfg(kani)]
#[kani::proof]
fn verify_clamp_contract() {
    let value: i16 = kani::any();
    let low: i16 = kani::any();
    let high: i16 = kani::any();
    let _ = clamp(value, low, high);
}

/// 示例 4：泛型循环不变量 —— 验证切片前缀均满足谓词
///
/// 使用 `#[kani::loop_invariant]` 证明：遍历过程中所有已访问元素
/// 都满足给定条件，且下标始终合法。
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn verify_all_positive_prefix_generic() {
    let arr: [i16; 4] = [kani::any(), kani::any(), kani::any(), kani::any()];
    kani::assume(kani::forall!(|i in 0..4| arr[i] > 0));

    let mut i = 0usize;
    #[kani::loop_invariant(i <= arr.len())]
    #[kani::loop_invariant(
        kani::forall!(|j in 0..i| arr[j] > 0)
    )]
    while i < arr.len() {
        assert!(arr[i] > 0);
        i += 1;
    }

    assert_eq!(i, arr.len());
    assert!(arr.iter().all(|&x| x > 0));
}
