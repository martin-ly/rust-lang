//! Rust 1.96 `gen` block 算法前瞻（nightly-only）
//!
//! 本模块包含使用 `gen {}` / `yield` 实现的惰性迭代器算法，
//! 需要 nightly 编译器启用 `#![feature(gen_blocks, yield_expr)]`。

// ==================== Rust 2024 Edition: gen blocks 算法前瞻 (nightly-only) ====================
// 说明: Rust 2024 Edition 本身已在 Rust 1.85.0 稳定；但 `gen {}` / `gen fn` 仍为 nightly。
// ⚠️ 注意: 以下代码需要 nightly 编译器和 `#![feature(gen_blocks, yield_expr)]`
// 本专题展示 `gen` 块在算法实现中的前瞻应用，stable 编译器不可用。

use std::collections::VecDeque;

/// 使用 gen 块实现斐波那契数列生成器
/// use gen implementation generator
///
/// 经典的无限序列生成，gen 块使实现极为简洁。
pub fn fibonacci_gen() -> impl Iterator<Item = u64> {
    gen {
        let (mut a, mut b) = (0u64, 1u64);
        loop {
            yield a;
            (a, b) = (b, a + b);
}
    }
}

/// 使用 gen 块实现素数筛（埃拉托斯特尼筛法）
///
/// 惰性生成素数，只在需要时计算下一个素数。
pub fn prime_sieve_gen(limit: usize) -> impl Iterator<Item = usize> {
    gen move {
        if limit >= 2 {
            yield 2;
        }
        let mut sieve = vec![true; limit + 1];
        for p in (3..=limit).step_by(2) {
            if sieve[p] {
                yield p;
                if p * p <= limit {
                    for multiple in (p * p..=limit).step_by(p * 2) {
                        sieve[multiple] = false;
                    }
                }
            }
        }
    }
}

/// 使用 gen 块实现滑动窗口迭代器
/// use gen implementation iterator
///
/// 在数据切片上滑动固定大小的窗口，产生每个窗口的内容。
pub fn sliding_window_gen<T: Clone>(data: &[T], size: usize) -> impl Iterator<Item = Vec<T>> + '_ {
    gen move {
        if size > 0 && size <= data.len() {
            for i in 0..=data.len() - size {
                yield data[i..i + size].to_vec();
            }
        }
    }
}

/// 二叉树节点定义
/// binary tree node definition
#[derive(Debug, PartialEq, Clone)]
pub struct TreeNode<T> {
    /// 节点值
    /// node value
    pub value: T,
    /// 左子树
    /// left tree
    pub left: Option<Box<TreeNode<T>>>,
    /// 右子树
    /// right tree
    pub right: Option<Box<TreeNode<T>>>,
}

impl<T: Clone> TreeNode<T> {
    /// 使用 gen 块实现前序遍历
    /// use gen implementationfront traversal
    ///
    /// 使用显式栈避免递归，gen 块让迭代器实现极为简洁。
    pub fn pre_order_gen(&self) -> impl Iterator<Item = T> + '_ {
        gen move {
            let mut stack = vec![self];
            while let Some(node) = stack.pop() {
                yield node.value.clone();
                if let Some(right) = &node.right {
                    stack.push(right);
                }
                if let Some(left) = &node.left {
                    stack.push(left);
                }
            }
        }
    }

    /// 使用 gen 块实现中序遍历
    /// use gen implementation traversal
    pub fn in_order_gen(&self) -> impl Iterator<Item = T> + '_ {
        gen move {
            let mut stack = Vec::new();
            let mut current: Option<&TreeNode<T>> = Some(self);
            while current.is_some() || !stack.is_empty() {
                while let Some(node) = current {
                    stack.push(node);
                    current = node.left.as_deref();
                }
                if let Some(node) = stack.pop() {
                    yield node.value.clone();
                    current = node.right.as_deref();
                }
            }
        }
    }

    /// 使用 gen 块实现层序遍历（BFS）
    pub fn level_order_gen(&self) -> impl Iterator<Item = T> + '_ {
        gen move {
            let mut queue = VecDeque::new();
            queue.push_back(self);
            while let Some(node) = queue.pop_front() {
                yield node.value.clone();
                if let Some(left) = &node.left {
                    queue.push_back(left);
                }
                if let Some(right) = &node.right {
                    queue.push_back(right);
                }
            }
        }
    }
}

/// 使用 gen 块实现笛卡尔积生成器
/// use gen implementation generator
///
/// 生成两个集合的所有可能组合。
/// set all may combination 。
pub fn cartesian_product_gen<A, B>(a: Vec<A>, b: Vec<B>) -> impl Iterator<Item = (A, B)>
where
    A: Clone + 'static,
    B: Clone + 'static,
{
    gen move {
        for x in a {
            for y in b.clone() {
                yield (x.clone(), y);
            }
        }
    }
}

/// 演示 gen blocks 算法特性
/// demonstration gen blocks algorithm feature
pub fn demonstrate_gen_block_algorithms() {
    println!("\n=== gen blocks 算法专题演示 ===\n");

    // 斐波那契
    println!("斐波那契数列 (前 10 个):");
    for (i, val) in fibonacci_gen().take(10).enumerate() {
        print!("F({})={} ", i, val);
    }
    println!();

    // 素数筛
    println!("\n100 以内的素数:");
    for p in prime_sieve_gen(100) {
        print!("{} ", p);
    }
    println!();

    // 滑动窗口
    println!("\n滑动窗口 (size=3):");
    let data = vec![1, 2, 3, 4, 5];
    for window in sliding_window_gen(&data, 3) {
        print!("{:?} ", window);
    }
    println!();

    // 树遍历
    println!("\n二叉树遍历:");
    let tree = TreeNode {
        value: 1,
        left: Some(Box::new(TreeNode {
            value: 2,
            left: Some(Box::new(TreeNode {
                value: 4,
                left: None,
                right: None,
            })),
            right: Some(Box::new(TreeNode {
                value: 5,
                left: None,
                right: None,
            })),
        })),
        right: Some(Box::new(TreeNode {
            value: 3,
            left: Some(Box::new(TreeNode {
                value: 6,
                left: None,
                right: None,
            })),
            right: Some(Box::new(TreeNode {
                value: 7,
                left: None,
                right: None,
            })),
        })),
    };
    println!("前序遍历: {:?}", tree.pre_order_gen().collect::<Vec<_>>());
    println!("中序遍历: {:?}", tree.in_order_gen().collect::<Vec<_>>());
    println!("层序遍历: {:?}", tree.level_order_gen().collect::<Vec<_>>());

    // 笛卡尔积
    println!("\n笛卡尔积 [1,2] x [\"a\",\"b\"]:");
    let cp: Vec<_> = cartesian_product_gen(vec![1, 2], vec!["a", "b"]).collect();
    println!("{:?}", cp);
}

#[cfg(test)]
mod gen_block_algorithm_tests {
    use super::*;

    #[test]
    fn test_fibonacci_gen() {
        let fib: Vec<u64> = fibonacci_gen().take(10).collect();
        assert_eq!(fib, vec![0, 1, 1, 2, 3, 5, 8, 13, 21, 34]);
    }

    #[test]
    fn test_prime_sieve_gen() {
        let primes: Vec<usize> = prime_sieve_gen(30).collect();
        assert_eq!(primes, vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]);
    }

    #[test]
    fn test_sliding_window_gen() {
        let data = vec![1, 2, 3, 4, 5];
        let windows: Vec<Vec<i32>> = sliding_window_gen(&data, 3).collect();
        assert_eq!(windows, vec![vec![1, 2, 3], vec![2, 3, 4], vec![3, 4, 5]]);
    }

    #[test]
    fn test_tree_pre_order_gen() {
        let tree = TreeNode {
            value: 1,
            left: Some(Box::new(TreeNode {
                value: 2,
                left: None,
                right: None,
            })),
            right: Some(Box::new(TreeNode {
                value: 3,
                left: None,
                right: None,
            })),
        };
        assert_eq!(tree.pre_order_gen().collect::<Vec<_>>(), vec![1, 2, 3]);
    }

    #[test]
    fn test_tree_in_order_gen() {
        let tree = TreeNode {
            value: 1,
            left: Some(Box::new(TreeNode {
                value: 2,
                left: None,
                right: None,
            })),
            right: Some(Box::new(TreeNode {
                value: 3,
                left: None,
                right: None,
            })),
        };
        assert_eq!(tree.in_order_gen().collect::<Vec<_>>(), vec![2, 1, 3]);
    }

    #[test]
    fn test_tree_level_order_gen() {
        let tree = TreeNode {
            value: 1,
            left: Some(Box::new(TreeNode {
                value: 2,
                left: None,
                right: None,
            })),
            right: Some(Box::new(TreeNode {
                value: 3,
                left: None,
                right: None,
            })),
        };
        assert_eq!(tree.level_order_gen().collect::<Vec<_>>(), vec![1, 2, 3]);
    }

    #[test]
    fn test_cartesian_product_gen() {
        let result: Vec<_> = cartesian_product_gen(vec![1, 2], vec!["a", "b"]).collect();
        assert_eq!(result, vec![(1, "a"), (1, "b"), (2, "a"), (2, "b")]);
    }
}

