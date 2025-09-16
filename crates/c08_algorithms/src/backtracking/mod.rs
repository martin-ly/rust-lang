//! 回溯算法：同步 / Rayon并行 / Tokio异步

use anyhow::Result;
use rayon::prelude::*;

/// 检查在 `row` 行把皇后放在 `col` 是否安全
fn is_safe(partial: &[usize], row: usize, col: usize) -> bool {
    for (r, &c) in partial.iter().enumerate() {
        if c == col {
            return false;
        }
        let dr = row as isize - r as isize;
        let dc = col as isize - c as isize;
        if dr.abs() == dc.abs() {
            return false;
        }
    }
    true
}

fn solve_sync_inner(
    n: usize,
    row: usize,
    partial: &mut Vec<usize>,
    solutions: &mut Vec<Vec<usize>>,
) {
    if row == n {
        solutions.push(partial.clone());
        return;
    }
    for col in 0..n {
        if is_safe(partial, row, col) {
            partial.push(col);
            solve_sync_inner(n, row + 1, partial, solutions);
            partial.pop();
        }
    }
}

/// 同步：返回所有解，每个解为长度为 n 的列索引数组
pub fn nqueens_solutions_sync(n: usize) -> Vec<Vec<usize>> {
    let mut solutions = Vec::new();
    let mut partial = Vec::with_capacity(n);
    solve_sync_inner(n, 0, &mut partial, &mut solutions);
    solutions
}

/// 并行：在首行的每个列位并行分支
pub fn nqueens_solutions_parallel(n: usize) -> Vec<Vec<usize>> {
    (0..n)
        .into_par_iter()
        .map(|first_col| {
            let mut local_solutions = Vec::new();
            let mut partial = vec![first_col];
            solve_sync_inner(n, 1, &mut partial, &mut local_solutions);
            local_solutions
        })
        .flatten()
        .collect()
}

/// 异步：spawn_blocking 包裹 CPU 密集型回溯
pub async fn nqueens_solutions_async(n: usize) -> Result<Vec<Vec<usize>>> {
    Ok(tokio::task::spawn_blocking(move || nqueens_solutions_parallel(n)).await?)
}

/// 仅返回解数量（同步）
pub fn nqueens_count_sync(n: usize) -> usize {
    nqueens_solutions_sync(n).len()
}

// =========================
// 全排列 / 子集生成（回溯）
// =========================

fn permute_sync_inner<T: Clone>(nums: &mut [T], start: usize, out: &mut Vec<Vec<T>>) {
    if start == nums.len() {
        out.push(nums.to_vec());
        return;
    }
    for i in start..nums.len() {
        nums.swap(start, i);
        permute_sync_inner(nums, start + 1, out);
        nums.swap(start, i);
    }
}

pub fn permutations_sync<T: Clone + Send>(mut nums: Vec<T>) -> Vec<Vec<T>> {
    let mut out = Vec::new();
    permute_sync_inner(&mut nums, 0, &mut out);
    out
}

pub fn permutations_parallel<T: Clone + Send + Sync>(nums: Vec<T>) -> Vec<Vec<T>> {
    (0..nums.len())
        .into_par_iter()
        .map(|i| {
            let mut local = Vec::new();
            let mut arr = nums.clone();
            arr.swap(0, i);
            permute_sync_inner(&mut arr, 1, &mut local);
            local
        })
        .flatten()
        .collect()
}

pub async fn permutations_async<T: Clone + Send + Sync + 'static>(
    nums: Vec<T>,
) -> Result<Vec<Vec<T>>> {
    Ok(tokio::task::spawn_blocking(move || permutations_parallel(nums)).await?)
}

pub fn subsets_sync<T: Clone>(nums: &[T]) -> Vec<Vec<T>> {
    let n = nums.len();
    let mut res = Vec::with_capacity(1 << n);
    let mut cur = Vec::new();
    fn dfs<T: Clone>(i: usize, nums: &[T], cur: &mut Vec<T>, out: &mut Vec<Vec<T>>) {
        if i == nums.len() {
            out.push(cur.clone());
            return;
        }
        dfs(i + 1, nums, cur, out);
        cur.push(nums[i].clone());
        dfs(i + 1, nums, cur, out);
        cur.pop();
    }
    dfs(0, nums, &mut cur, &mut res);
    res
}

pub fn subsets_parallel<T: Clone + Send + Sync>(nums: &[T]) -> Vec<Vec<T>> {
    let n = nums.len();
    let half = n / 2;
    let left = &nums[..half];
    let right = &nums[half..];
    let (a, b): (Vec<Vec<T>>, Vec<Vec<T>>) =
        rayon::join(|| subsets_sync(left), || subsets_sync(right));
    // 笛卡尔积合并（避免借用生命周期问题：克隆 b 进入闭包）
    a.into_par_iter()
        .flat_map_iter(move |l| {
            let b_local = b.clone();
            b_local.into_iter().map(move |r| {
                let mut v = l.clone();
                v.extend(r);
                v
            })
        })
        .collect()
}

pub async fn subsets_async<T: Clone + Send + Sync + 'static>(nums: Vec<T>) -> Result<Vec<Vec<T>>> {
    Ok(tokio::task::spawn_blocking(move || subsets_parallel(&nums)).await?)
}

/// 仅返回解数量（并行）
pub fn nqueens_count_parallel(n: usize) -> usize {
    nqueens_solutions_parallel(n).len()
}

#[cfg(test)]
mod tests {
    use super::*;

    // 经典 N 皇后解数量：4->2, 5->10, 6->4, 7->40, 8->92
    #[test]
    fn test_nqueens_counts_sync() {
        assert_eq!(nqueens_count_sync(4), 2);
        assert_eq!(nqueens_count_sync(5), 10);
        assert_eq!(nqueens_count_sync(6), 4);
    }

    #[test]
    fn test_nqueens_parallel_and_async() {
        assert_eq!(nqueens_count_parallel(4), 2);

        let rt = tokio::runtime::Runtime::new().unwrap();
        let count8 = rt.block_on(async { nqueens_solutions_async(8).await.unwrap().len() });
        assert_eq!(count8, 92);
    }

    #[test]
    fn test_permutations_and_subsets() {
        let p = permutations_sync(vec![1, 2, 3]);
        assert_eq!(p.len(), 6);
        let s = subsets_sync(&[1, 2, 3]);
        assert_eq!(s.len(), 8);
    }
}
