//! Rust 1.98 Nightly 前瞻 —— 生成器块与新标准库 API
//!
//! 本模块包含两类内容：
//! - `gen { yield ... }` 生成器块在算法中的惰性序列应用
//! - 有望在 Rust 1.98.0 stable 中稳定化的标准库 API 示例
//!
//! **编译要求**: nightly Rust（启用 `gen_blocks`、`yield_expr`）
#![allow(clippy::incompatible_msrv)]

use std::ffi::CStr;
use std::net::Ipv6Addr;
use std::num::NonZeroU32;
use std::pin::pin;
use std::ptr;
use std::task::Waker;

/// # Rust 1.98 Nightly 算法与 API 前瞻
///
/// 用于展示 nightly 1.98 特性的入口结构体。
pub struct Rust198AlgorithmFeatures;

impl Rust198AlgorithmFeatures {
    /// 使用 gen 块生成惰性斐波那契序列。
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

    /// 使用 gen 块实现埃拉托斯特尼筛法（惰性素数序列）。
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

    /// 使用 gen 块生成二叉树的前序遍历序列。
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

    /// 使用 gen 块实现滑动窗口最大值（流式算法）。
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

/// 二叉树节点定义（用于遍历算法）。
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
    /// 创建新的叶子节点。
    pub fn new(val: T) -> Self {
        Self {
            val,
            left: None,
            right: None,
        }
    }

    /// 添加左子节点。
    pub fn left(mut self, node: TreeNode<T>) -> Self {
        self.left = Some(Box::new(node));
        self
    }

    /// 添加右子节点。
    pub fn right(mut self, node: TreeNode<T>) -> Self {
        self.right = Some(Box::new(node));
        self
    }
}

/// 演示 `isqrt` 整数平方根 API。
///
/// Rust 1.98.0 有望稳定有符号/无符号整数的 `isqrt`，
/// 以及 `NonZero<u*>` 的 `isqrt`。
pub fn demo_isqrt() {
    assert_eq!(25i32.isqrt(), 5);
    assert_eq!(25u32.isqrt(), 5);
    let nz = NonZeroU32::new(25).unwrap();
    assert_eq!(nz.isqrt().get(), 5);
}

/// 演示 strict provenance 相关指针 API。
///
/// `with_exposed_provenance`、`without_provenance`、`dangling` 等 API
/// 帮助逐步迁移到更严格的 provenance 模型。
pub fn demo_provenance() {
    let addr = 0usize;
    let _ptr: *const u8 = ptr::with_exposed_provenance(addr);
    let _ptr: *const u8 = ptr::without_provenance::<u8>(addr);
    let _ptr: *const u8 = ptr::dangling::<u8>();
}

/// 演示 IPv6 地址分类辅助方法。
pub fn demo_ipv6_classify() {
    let unique_local = Ipv6Addr::new(0xfc00, 0, 0, 0, 0, 0, 0, 1);
    let link_local = Ipv6Addr::new(0xfe80, 0, 0, 0, 0, 0, 0, 1);
    assert!(unique_local.is_unique_local());
    assert!(link_local.is_unicast_link_local());
}

/// 演示 `CStr::from_bytes_until_nul`。
///
/// 从字节切片构造 `CStr`，遇到第一个 NUL 字节即停止。
pub fn demo_cstr_from_bytes_until_nul() {
    let bytes = b"hello\0world";
    let cstr = CStr::from_bytes_until_nul(bytes).expect("valid C string");
    assert_eq!(cstr.to_str().unwrap(), "hello");
}

/// 演示 `std::pin::pin!` 宏。
///
/// 在栈上创建一个 pinned 值，无需手动 `Pin::new_unchecked`。
pub fn demo_pin_macro() {
    let pinned = pin!(42);
    assert_eq!(*pinned, 42);
}

/// 演示 `impl From<bool> for f32 / f64`。
pub fn demo_bool_to_float() {
    let x: f32 = true.into();
    let y: f64 = false.into();
    assert_eq!(x, 1.0);
    assert_eq!(y, 0.0);
}

/// 演示 `Waker::noop`。
///
/// 提供一个不执行任何操作的 Waker，方便测试与占位。
pub fn demo_waker_noop() {
    let waker: &Waker = Waker::noop();
    waker.wake_by_ref();
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

    #[test]
    fn test_198_api_demos() {
        demo_isqrt();
        demo_provenance();
        demo_ipv6_classify();
        demo_cstr_from_bytes_until_nul();
        demo_pin_macro();
        demo_bool_to_float();
        demo_waker_noop();
    }
}
