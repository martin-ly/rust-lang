//! Rust 1.98 Nightly 前瞻 —— 生成器块与算法
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.98 Nightly 算法前瞻
///
/// 本模块展示 nightly 1.98 中 `gen { yield ... }` 块在算法场景的应用：
/// - 惰性序列生成（斐波那契、素数筛）
/// - 树/图的遍历生成器
/// - 流式数据管道
///
/// **⚠️ 需要 nightly Rust + `#![feature(gen_blocks, yield_expr)]`**
pub struct Rust198AlgorithmFeatures;

impl Rust198AlgorithmFeatures {
    /// 使用 gen 块生成惰性斐波那契序列
    ///
    /// 对比 `std::iter::from_fn`，`gen` 块语法更直观，无需显式闭包包装。
    pub fn fibonacci() -> impl Iterator<Item = u64> {
        gen {
            let (mut a, mut b) = (0, 1);
            loop {
                yield a;
                (a, b) = (b, a + b);
            }
        }
    }

    /// 使用 gen 块实现埃拉托斯特尼筛法（惰性素数序列）
    ///
    /// 每次 `yield` 产生一个素数，然后筛去其倍数。算法惰性执行，
    /// 只计算被请求的素数数量。
    pub fn primes() -> impl Iterator<Item = u64> {
        gen {
            let mut sieve = vec![true; 1_000_000];
            sieve[0] = false;
            sieve[1] = false;
            for p in 2..sieve.len() {
                if sieve[p] {
                    yield p as u64;
                    for multiple in (p * p..sieve.len()).step_by(p) {
                        sieve[multiple] = false;
                    }
                }
            }
        }
    }

    /// 使用 gen 块生成二叉树的前序遍历序列
    ///
    /// 利用显式栈在 gen 块中惰性 yield 节点值，无需一次性构造完整 Vec。
    pub fn preorder_traversal<T: Clone>(tree: Option<Box<TreeNode<T>>>) -> impl Iterator<Item = T> {
        gen move {
            let mut stack = Vec::new();
            if let Some(root) = tree {
                stack.push(root);
            }
            while let Some(node) = stack.pop() {
                yield node.val;
                if let Some(right) = node.right {
                    stack.push(right);
                }
                if let Some(left) = node.left {
                    stack.push(left);
                }
            }
        }
    }

    /// 使用 gen 块实现滑动窗口最大值（流式算法）
    ///
    /// 接收一个数据流，维护大小为 `k` 的窗口，每次 yield 当前窗口最大值。
    pub fn sliding_window_max(stream: Vec<i32>, k: usize) -> impl Iterator<Item = i32> {
        gen move {
            let n = stream.len();
            if k == 0 || n < k {
                return;
            }
            let mut deque: Vec<usize> = Vec::new();
            for i in 0..n {
                let val = stream[i];
                // 移除窗口外的元素
                while let Some(&front) = deque.first() {
                    if front + k <= i {
                        deque.remove(0);
                    } else {
                        break;
                    }
                }
                // 移除比当前值小的元素（它们不可能成为最大值）
                while let Some(&back) = deque.last() {
                    if stream[back] <= val {
                        deque.pop();
                    } else {
                        break;
                    }
                }
                deque.push(i);
                if i >= k - 1 {
                    yield stream[*deque.first().unwrap()];
                }
            }
        }
    }
}

/// 二叉树节点定义（用于遍历算法）
#[derive(Debug, Clone)]
pub struct TreeNode<T> {
    /// 节点值
    pub val: T,
    /// 左子树
    pub left: Option<Box<TreeNode<T>>>,
    /// 右子树
    pub right: Option<Box<TreeNode<T>>>,
}

impl<T> TreeNode<T> {
    /// 创建新的叶子节点
    pub fn new(val: T) -> Self {
        Self {
            val,
            left: None,
            right: None,
        }
    }

    /// 添加左子节点
    pub fn left(mut self, node: TreeNode<T>) -> Self {
        self.left = Some(Box::new(node));
        self
    }

    /// 添加右子节点
    pub fn right(mut self, node: TreeNode<T>) -> Self {
        self.right = Some(Box::new(node));
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fibonacci() {
        let fib: Vec<u64> = Rust198AlgorithmFeatures::fibonacci().take(10).collect();
        assert_eq!(fib, vec![0, 1, 1, 2, 3, 5, 8, 13, 21, 34]);
    }

    #[test]
    fn test_primes() {
        let primes: Vec<u64> = Rust198AlgorithmFeatures::primes().take(10).collect();
        assert_eq!(primes, vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]);
    }

    #[test]
    fn test_preorder_traversal() {
        let tree = Some(Box::new(
            TreeNode::new(2)
                .left(TreeNode::new(1))
                .right(TreeNode::new(3)),
        ));
        let vals: Vec<i32> = Rust198AlgorithmFeatures::preorder_traversal(tree).collect();
        assert_eq!(vals, vec![2, 1, 3]);
    }

    #[test]
    fn test_sliding_window_max() {
        let stream = vec![1, 3, -1, -3, 5, 3, 6, 7];
        let result: Vec<i32> = Rust198AlgorithmFeatures::sliding_window_max(stream, 3).collect();
        assert_eq!(result, vec![3, 3, 5, 5, 6, 7]);
    }
}
