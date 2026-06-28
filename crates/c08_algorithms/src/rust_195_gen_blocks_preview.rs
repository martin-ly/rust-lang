//! Rust 1.95 `gen` block 算法前瞻（nightly-only）
//!
//! 本模块包含使用 `gen {}` / `yield` 实现的惰性迭代器算法，
//! 需要 nightly 编译器启用 `#![feature(gen_blocks, yield_expr)]`。

/// 演示 Rust 1.95 `gen` block 在算法中的前瞻应用。
pub struct RealRust195GenBlocks;

impl RealRust195GenBlocks {
    /// `gen` block yielding even numbers from a slice
    pub fn gen_even_numbers(items: &[i32]) -> impl Iterator<Item = i32> + '_ {
        gen move {
            for &item in items {
                if item % 2 == 0 {
                    yield item;
                }
            }
        }
    }

    /// `gen` block: 合并 K 个已排序序列（K-way merge）
    pub fn gen_merge_sorted(sequences: Vec<Vec<i32>>) -> impl Iterator<Item = i32> {
        gen move {
            let mut iters: Vec<_> = sequences
                .into_iter()
                .map(|v| v.into_iter().peekable())
                .collect();

            loop {
                let min_val = iters
                    .iter_mut()
                    .filter_map(|iter| iter.peek().copied())
                    .min();

                if let Some(min) = min_val {
                    for iter in &mut iters {
                        if iter.peek() == Some(&min) {
                            iter.next();
                        }
                    }
                    yield min;
                } else {
                    break;
                }
            }
        }
    }

    /// `gen` block: 已排序序列去重
    pub fn gen_dedup_sorted(data: Vec<i32>) -> impl Iterator<Item = i32> {
        gen move {
            let mut iter = data.into_iter().peekable();
            while let Some(current) = iter.next() {
                while iter.peek() == Some(&current) {
                    iter.next();
                }
                yield current;
            }
        }
    }

    /// `gen` block: 滑动窗口求和
    pub fn gen_window_sum(data: Vec<i32>, window_size: usize) -> impl Iterator<Item = i32> {
        gen move {
            if window_size == 0 || data.len() < window_size {
                return;
            }
            for i in 0..=data.len() - window_size {
                let sum: i32 = data[i..i + window_size].iter().sum();
                yield sum;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gen_even_numbers() {
        let items = vec![1, 2, 3, 4, 5, 6];
        let evens: Vec<i32> = RealRust195GenBlocks::gen_even_numbers(&items).collect();
        assert_eq!(evens, vec![2, 4, 6]);
    }

    #[test]
    fn test_gen_merge_sorted() {
        let a = vec![1, 3, 5];
        let b = vec![2, 4, 6];
        let c = vec![0, 7];
        let merged: Vec<i32> = RealRust195GenBlocks::gen_merge_sorted(vec![a, b, c]).collect();
        assert_eq!(merged, vec![0, 1, 2, 3, 4, 5, 6, 7]);
    }

    #[test]
    fn test_gen_merge_sorted_empty() {
        let merged: Vec<i32> = RealRust195GenBlocks::gen_merge_sorted(vec![]).collect();
        assert!(merged.is_empty());
    }

    #[test]
    fn test_gen_dedup_sorted() {
        let data = vec![1, 1, 2, 2, 2, 3, 3, 4, 5, 5];
        let deduped: Vec<i32> = RealRust195GenBlocks::gen_dedup_sorted(data).collect();
        assert_eq!(deduped, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_gen_dedup_sorted_empty() {
        let deduped: Vec<i32> = RealRust195GenBlocks::gen_dedup_sorted(vec![]).collect();
        assert!(deduped.is_empty());
    }

    #[test]
    fn test_gen_window_sum() {
        let data = vec![1, 2, 3, 4, 5];
        let sums: Vec<i32> = RealRust195GenBlocks::gen_window_sum(data, 3).collect();
        assert_eq!(sums, vec![6, 9, 12]); // 1+2+3, 2+3+4, 3+4+5
    }

    #[test]
    fn test_gen_window_sum_empty() {
        let sums: Vec<i32> = RealRust195GenBlocks::gen_window_sum(vec![], 3).collect();
        assert!(sums.is_empty());
    }
}
