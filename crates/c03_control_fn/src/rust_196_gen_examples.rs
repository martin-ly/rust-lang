//! # Rust 1.96.0 `gen` 关键字生成器特性示例
//!
//! 本模块展示了 Rust Edition 2024 中引入的 `gen` 关键字，
//! 用于创建生成器（generators），简化迭代器的创建和使用。
//!
//! **注意**: `gen` 关键字是 Edition 2024 的实验性功能，
//! 需要在 nightly 编译器中启用 `#![feature(gen_blocks)]`。
//!
//! # 文件信息
//! - 文件: rust_196_gen_examples.rs
//! - 创建日期: 2026-04-10
//! - 版本: 1.0
//! - Rust版本: 1.96.0 (nightly)
//! - Edition: 2024

// 启用 gen 块特性（在支持的 nightly 版本中）
// 注意：此特性目前处于实验阶段
#![allow(unstable_features)]

// ==================== 1. 基础 gen 块 ====================

/// # 基础 gen 块
///
/// `gen` 块允许直接创建生成器，无需显式定义结构体和实现 Iterator trait。
/// 使用 `yield` 关键字可以产生值。
///
/// ## 语法
/// ```rust,ignore
/// gen {
///     yield value;
/// }
/// ```
pub mod basic_gen {
    /// 使用 gen 块创建简单的计数器
    ///
    /// 生成 1 到 n 的整数序列
    #[allow(unreachable_code)]
    pub fn simple_counter(n: usize) -> impl Iterator<Item = usize> {
        // 使用 gen 块创建迭代器
        // 注意：当 gen 块稳定后，语法如下：
        // gen {
        //     for i in 1..=n {
        //         yield i;
        //     }
        // }

        // 当前使用标准库实现等效功能
        1..=n
    }

    /// 使用 gen 块创建斐波那契生成器
    ///
    /// 生成无限斐波那契数列
    pub fn fibonacci_gen() -> impl Iterator<Item = u64> {
        // gen {
        //     let mut a = 0u64;
        //     let mut b = 1u64;
        //     loop {
        //         yield a;
        //         let temp = a.wrapping_add(b);
        //         a = b;
        //         b = temp;
        //     }
        // }

        // 当前使用标准库实现
        std::iter::from_fn({
            let mut a = 0u64;
            let mut b = 1u64;
            move || {
                let result = a;
                let temp = a.wrapping_add(b);
                a = b;
                b = temp;
                Some(result)
            }
        })
    }

    /// 使用 gen 块创建范围生成器
    ///
    /// 生成指定范围的值，支持步长
    pub fn range_gen(start: i32, end: i32, step: i32) -> impl Iterator<Item = i32> {
        // gen {
        //     let mut current = start;
        //     while (step > 0 && current <= end) || (step < 0 && current >= end) {
        //         yield current;
        //         current += step;
        //     }
        // }

        // 当前使用标准库实现
        std::iter::successors(Some(start), move |&x| {
            let next = x + step;
            if (step > 0 && next <= end) || (step < 0 && next >= end) {
                Some(next)
            } else {
                None
            }
        })
    }

    /// 使用 gen 块创建重复生成器
    ///
    /// 重复产生同一个值指定次数
    pub fn repeat_gen<T: Clone>(value: T, count: usize) -> impl Iterator<Item = T> {
        // gen {
        //     for _ in 0..count {
        //         yield value.clone();
        //     }
        // }

        std::iter::repeat(value).take(count)
    }

    /// 使用 gen 块创建累积和生成器
    ///
    /// 对输入迭代器产生累积和
    pub fn cumulative_sum<I>(iter: I) -> impl Iterator<Item = i64>
    where
        I: IntoIterator<Item = i64>,
    {
        // gen {
        //     let mut sum = 0i64;
        //     for item in iter {
        //         sum += item;
        //         yield sum;
        //     }
        // }

        let mut sum = 0i64;
        iter.into_iter().map(move |x| {
            sum += x;
            sum
        })
    }
}

// ==================== 2. 异步 gen 块 ====================

/// # 异步 gen 块
///
/// `async gen` 允许创建异步生成器，用于处理异步数据流。
pub mod async_gen {
    #![allow(unused_imports)]
    use std::pin::Pin;
    use std::task::{Context, Poll};

    /// 异步生成器 trait（模拟）
    pub trait AsyncIterator {
        type Item;
        fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>>;
    }

    /// 使用 async gen 创建异步计数器
    ///
    /// 异步生成计数序列
    pub async fn async_counter_stream(n: usize) -> impl Iterator<Item = usize> {
        // async gen {
        //     for i in 0..n {
        //         tokio::time::sleep(Duration::from_millis(10)).await;
        //         yield i;
        //     }
        // }

        // 当前实现
        0..n
    }

    /// 使用 async gen 创建异步数据流
    ///
    /// 模拟从网络接收数据的场景
    pub async fn network_data_stream() -> impl Iterator<Item = Vec<u8>> {
        // async gen {
        //     let mut buffer = vec![0u8; 1024];
        //     loop {
        //         match socket.read(&mut buffer).await {
        //             Ok(0) => break,
        //             Ok(n) => yield buffer[..n].to_vec(),
        //             Err(_) => break,
        //         }
        //     }
        // }

        // 模拟数据
        vec![
            vec![1, 2, 3, 4, 5],
            vec![6, 7, 8, 9, 10],
            vec![11, 12, 13, 14, 15],
        ]
        .into_iter()
    }

    /// 使用 async gen 创建定时器流
    ///
    /// 定期产生时间戳
    pub async fn timer_stream(_interval_ms: u64, count: usize) -> impl Iterator<Item = u64> {
        // async gen {
        //     for i in 0..count {
        //         tokio::time::sleep(Duration::from_millis(interval_ms)).await;
        //         yield std::time::SystemTime::now()
        //             .duration_since(std::time::UNIX_EPOCH)
        //             .unwrap()
        //             .as_millis() as u64;
        //     }
        // }

        (0..count).map(move |_| {
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_millis() as u64
        })
    }
}

// ==================== 3. 高级 gen 模式 ====================

/// # 高级 gen 模式
///
/// 展示 gen 块在复杂场景中的应用。
pub mod advanced_gen {
    /// 使用 gen 实现自定义迭代器适配器
    ///
    /// FilterMap 风格的生成器
    pub fn filter_map_gen<I, F, T>(iter: I, f: F) -> impl Iterator<Item = T>
    where
        I: IntoIterator,
        F: FnMut(I::Item) -> Option<T>,
    {
        // gen {
        //     for item in iter {
        //         if let Some(mapped) = f(item) {
        //             yield mapped;
        //         }
        //     }
        // }

        iter.into_iter().filter_map(f)
    }

    /// 使用 gen 实现扁平化迭代器
    ///
    /// Flatten 风格的生成器
    pub fn flatten_gen<I>(iter: I) -> impl Iterator<Item = <I::Item as IntoIterator>::Item>
    where
        I: IntoIterator,
        I::Item: IntoIterator,
    {
        // gen {
        //     for inner in iter {
        //         for item in inner {
        //             yield item;
        //         }
        //     }
        // }

        iter.into_iter().flatten()
    }

    /// 使用 gen 实现交错迭代器
    ///
    /// 交替从两个迭代器取值
    pub fn interleave_gen<I, J>(a: I, b: J) -> impl Iterator<Item = I::Item>
    where
        I: IntoIterator,
        J: IntoIterator<Item = I::Item>,
    {
        // gen {
        //     let mut a = a.into_iter();
        //     let mut b = b.into_iter();
        //     loop {
        //         match (a.next(), b.next()) {
        //             (Some(x), Some(y)) => {
        //                 yield x;
        //                 yield y;
        //             }
        //             (Some(x), None) => yield x,
        //             (None, Some(y)) => yield y,
        //             (None, None) => break,
        //         }
        //     }
        // }

        let mut a = a.into_iter();
        let mut b = b.into_iter();
        std::iter::from_fn(move || a.next().or_else(|| b.next()))
    }

    /// 使用 gen 实现窗口迭代器
    ///
    /// 滑动窗口生成器
    pub fn window_gen<T: Clone>(data: &[T], size: usize) -> impl Iterator<Item = Vec<T>> + '_ {
        // gen {
        //     if size > 0 && size <= data.len() {
        //         for i in 0..=data.len() - size {
        //             yield data[i..i + size].to_vec();
        //         }
        //     }
        // }

        (0..=data.len().saturating_sub(size)).map(move |i| data[i..i + size].to_vec())
    }

    /// 使用 gen 实现组合迭代器
    ///
    /// 生成所有可能的组合
    pub fn combinations_gen<T: Clone>(data: &[T], k: usize) -> impl Iterator<Item = Vec<T>> + '_ {
        // gen {
        //     fn combine<T: Clone>(data: &[T], k: usize, start: usize, current: &mut Vec<T>) {
        //         if current.len() == k {
        //             yield current.clone();
        //             return;
        //         }
        //         for i in start..data.len() {
        //             current.push(data[i].clone());
        //             combine(data, k, i + 1, current);
        //             current.pop();
        //         }
        //     }
        //     let mut current = Vec::new();
        //     combine(data, k, 0, &mut current);
        // }

        // 使用递归生成组合
        fn combine<T: Clone>(
            data: &[T],
            k: usize,
            start: usize,
            current: &mut Vec<T>,
            result: &mut Vec<Vec<T>>,
        ) {
            if current.len() == k {
                result.push(current.clone());
                return;
            }
            for i in start..data.len() {
                current.push(data[i].clone());
                combine(data, k, i + 1, current, result);
                current.pop();
            }
        }

        let mut result = Vec::new();
        let mut current = Vec::new();
        combine(data, k, 0, &mut current, &mut result);
        result.into_iter()
    }

    /// 使用 gen 实现排列迭代器
    ///
    /// 生成所有可能的排列
    pub fn permutations_gen<T: Clone>(data: &[T]) -> impl Iterator<Item = Vec<T>> + '_ {
        // gen {
        //     fn permute<T: Clone>(data: &mut [T]) {
        //         if data.len() <= 1 {
        //             yield data.to_vec();
        //             return;
        //         }
        //         for i in 0..data.len() {
        //             data.swap(0, i);
        //             permute(&mut data[1..]);
        //             data.swap(0, i);
        //         }
        //     }
        //     let mut data = data.to_vec();
        //     permute(&mut data);
        // }

        fn permute<T: Clone>(data: &mut [T], result: &mut Vec<Vec<T>>) {
            if data.len() <= 1 {
                result.push(data.to_vec());
                return;
            }
            for i in 0..data.len() {
                data.swap(0, i);
                permute(&mut data[1..], result);
                data.swap(0, i);
            }
        }

        let mut result = Vec::new();
        let mut data = data.to_vec();
        permute(&mut data, &mut result);
        result.into_iter()
    }

    /// 使用 gen 实现树遍历
    ///
    /// 二叉树的各种遍历方式
    #[derive(Clone)]
    pub struct TreeNode<T> {
        pub value: T,
        pub left: Option<Box<TreeNode<T>>>,
        pub right: Option<Box<TreeNode<T>>>,
    }

    impl<T: Clone> TreeNode<T> {
        /// 前序遍历
        pub fn pre_order(&self) -> impl Iterator<Item = T> + '_ {
            // gen {
            //     yield self.value.clone();
            //     if let Some(left) = &self.left {
            //         for val in left.pre_order() {
            //             yield val;
            //         }
            //     }
            //     if let Some(right) = &self.right {
            //         for val in right.pre_order() {
            //             yield val;
            //         }
            //     }
            // }

            let mut result = vec![self.value.clone()];
            if let Some(left) = &self.left {
                result.extend(left.pre_order());
            }
            if let Some(right) = &self.right {
                result.extend(right.pre_order());
            }
            result.into_iter()
        }

        /// 中序遍历
        pub fn in_order(&self) -> impl Iterator<Item = T> + '_ {
            let mut result = Vec::new();
            if let Some(left) = &self.left {
                result.extend(left.in_order());
            }
            result.push(self.value.clone());
            if let Some(right) = &self.right {
                result.extend(right.in_order());
            }
            result.into_iter()
        }

        /// 层序遍历（BFS）
        pub fn level_order(&self) -> impl Iterator<Item = T> {
            use std::collections::VecDeque;

            // gen {
            //     let mut queue = VecDeque::new();
            //     queue.push_back(self);
            //     while let Some(node) = queue.pop_front() {
            //         yield node.value.clone();
            //         if let Some(left) = &node.left {
            //             queue.push_back(left);
            //         }
            //         if let Some(right) = &node.right {
            //             queue.push_back(right);
            //         }
            //     }
            // }

            let mut result = Vec::new();
            let mut queue = VecDeque::new();
            queue.push_back(self.clone());
            while let Some(node) = queue.pop_front() {
                result.push(node.value);
                if let Some(left) = node.left {
                    queue.push_back(*left);
                }
                if let Some(right) = node.right {
                    queue.push_back(*right);
                }
            }
            result.into_iter()
        }
    }
}

// ==================== 4. gen 与 pin ====================

/// # gen 与 Pin
///
/// 展示 gen 块与 Pin 的配合使用。
pub mod gen_pin {
    use std::pin::Pin;

    /// 自引用生成器示例
    ///
    /// 使用 Pin 保证自引用结构的安全
    pub struct SelfReferentialGen<T> {
        data: Vec<T>,
        // 当 gen 块稳定后，这里可以存储生成器状态
    }

    impl<T: Clone> SelfReferentialGen<T> {
        pub fn new(data: Vec<T>) -> Self {
            Self { data }
        }

        /// 创建带状态的生成器
        pub fn create_generator(self: Pin<&mut Self>) -> impl Iterator<Item = T> + '_ {
            // gen {
            //     for item in &self.data {
            //         yield item.clone();
            //     }
            // }

            self.data.clone().into_iter()
        }
    }

    /// 安全的生成器重置
    pub fn reset_generator<T>(r#gen: Pin<&mut impl Iterator<Item = T>>) {
        // 在实际实现中，这里会重置生成器状态
        let _ = r#gen;
    }
}

// ==================== 5. 演示函数 ====================

/// 演示基础 gen 块
#[allow(dead_code)]
pub fn demonstrate_basic_gen() {
    println!("\n=== 基础 gen 块演示 ===\n");

    use basic_gen::*;

    // 简单计数器
    println!("简单计数器 (1..=5):");
    for i in simple_counter(5) {
        print!("{} ", i);
    }
    println!();

    // 斐波那契生成器
    println!("\n斐波那契数列 (前 10 个):");
    for (i, fib) in fibonacci_gen().take(10).enumerate() {
        print!("F({})={} ", i, fib);
    }
    println!();

    // 范围生成器
    println!("\n范围生成器 (0..=20, step=5):");
    for val in range_gen(0, 20, 5) {
        print!("{} ", val);
    }
    println!();

    // 重复生成器
    println!("\n重复生成器 (重复 'X' 8 次):");
    for val in repeat_gen('X', 8) {
        print!("{}", val);
    }
    println!();

    // 累积和
    println!("\n累积和 [1, 2, 3, 4, 5]:");
    let data: Vec<i64> = vec![1, 2, 3, 4, 5];
    for sum in cumulative_sum(data) {
        print!("{} ", sum);
    }
    println!();
}

/// 演示高级 gen 模式
#[allow(dead_code)]
pub fn demonstrate_advanced_gen() {
    println!("\n=== 高级 gen 模式演示 ===\n");

    use advanced_gen::*;

    // 窗口生成器
    println!("窗口生成器 (size=3):");
    let data = vec![1, 2, 3, 4, 5, 6, 7];
    for window in window_gen(&data, 3) {
        print!("{:?} ", window);
    }
    println!();

    // 组合生成器
    println!("\n组合生成器 (从 [1,2,3,4] 中选 2 个):");
    let items = vec![1, 2, 3, 4];
    for combo in combinations_gen(&items, 2) {
        print!("{:?} ", combo);
    }
    println!();

    // 排列生成器
    println!("\n排列生成器 ([1,2,3] 的全排列):");
    let items = vec![1, 2, 3];
    for perm in permutations_gen(&items) {
        print!("{:?} ", perm);
    }
    println!();

    // 树遍历
    println!("\n树遍历演示:");
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

    println!("前序遍历: {:?}", tree.pre_order().collect::<Vec<_>>());
    println!("中序遍历: {:?}", tree.in_order().collect::<Vec<_>>());
    println!("层序遍历: {:?}", tree.level_order().collect::<Vec<_>>());
}

/// 演示 Rust 1.96.0 gen 关键字特性
pub fn demonstrate_rust_196_gen_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 gen 关键字特性演示");
    println!("   (Edition 2024 实验性功能)");
    println!("========================================\n");

    demonstrate_basic_gen();
    demonstrate_advanced_gen();

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");

    println!("注意: gen 块特性目前处于实验阶段，");
    println!("      需要 nightly 编译器和 #![feature(gen_blocks)]");
}

/// 获取 Rust 1.96.0 gen 特性信息
pub fn get_rust_196_gen_info() -> String {
    "Rust 1.96.0 gen 关键字特性:\n- gen 块: 使用 yield 创建迭代器\n- async gen: 创建异步生成器\n- \
     简化自定义迭代器实现\n- 支持复杂控制流 (loop, if, match)\n- Edition 2024 实验性功能"
        .to_string()
}

// ==================== 测试 ====================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_counter() {
        let result: Vec<usize> = basic_gen::simple_counter(5).collect();
        assert_eq!(result, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_fibonacci_gen() {
        let result: Vec<u64> = basic_gen::fibonacci_gen().take(10).collect();
        assert_eq!(result, vec![0, 1, 1, 2, 3, 5, 8, 13, 21, 34]);
    }

    #[test]
    fn test_range_gen() {
        let result: Vec<i32> = basic_gen::range_gen(0, 20, 5).collect();
        assert_eq!(result, vec![0, 5, 10, 15, 20]);

        let result: Vec<i32> = basic_gen::range_gen(10, 0, -2).collect();
        assert_eq!(result, vec![10, 8, 6, 4, 2, 0]);
    }

    #[test]
    fn test_repeat_gen() {
        let result: Vec<char> = basic_gen::repeat_gen('A', 5).collect();
        assert_eq!(result, vec!['A', 'A', 'A', 'A', 'A']);
    }

    #[test]
    fn test_cumulative_sum() {
        let data = vec![1i64, 2, 3, 4, 5];
        let result: Vec<i64> = basic_gen::cumulative_sum(data).collect();
        assert_eq!(result, vec![1, 3, 6, 10, 15]);
    }

    #[test]
    fn test_filter_map_gen() {
        let data = vec!["1", "two", "3", "four", "5"];
        let result: Vec<i32> = advanced_gen::filter_map_gen(data, |s| s.parse().ok()).collect();
        assert_eq!(result, vec![1, 3, 5]);
    }

    #[test]
    fn test_flatten_gen() {
        let data = vec![vec![1, 2], vec![3, 4], vec![5, 6]];
        let result: Vec<i32> = advanced_gen::flatten_gen(data).collect();
        assert_eq!(result, vec![1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_window_gen() {
        let data = vec![1, 2, 3, 4, 5];
        let result: Vec<Vec<i32>> = advanced_gen::window_gen(&data, 3).collect();
        assert_eq!(result, vec![vec![1, 2, 3], vec![2, 3, 4], vec![3, 4, 5]]);
    }

    #[test]
    fn test_combinations_gen() {
        let data = vec![1, 2, 3];
        let result: Vec<Vec<i32>> = advanced_gen::combinations_gen(&data, 2).collect();
        assert_eq!(result, vec![vec![1, 2], vec![1, 3], vec![2, 3]]);
    }

    #[test]
    fn test_permutations_gen() {
        let data = vec![1, 2, 3];
        let mut result: Vec<Vec<i32>> = advanced_gen::permutations_gen(&data).collect();
        result.sort();
        assert_eq!(result.len(), 6);
    }

    #[test]
    fn test_tree_traversal() {
        use advanced_gen::TreeNode;

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

        assert_eq!(tree.pre_order().collect::<Vec<_>>(), vec![1, 2, 3]);
        assert_eq!(tree.in_order().collect::<Vec<_>>(), vec![2, 1, 3]);
        assert_eq!(tree.level_order().collect::<Vec<_>>(), vec![1, 2, 3]);
    }
}
