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
