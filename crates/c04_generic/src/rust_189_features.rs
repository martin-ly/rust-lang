//! # Rust 1.89 特性示例 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features.rs`
//!
//! ## 版本历史说明
//!
//! 本文件展示 Rust 1.89 版本的特性，当前项目已升级到 Rust 1.92.0。
//!
//! ### Rust 1.92.0 主要改进
//!
//! - **语言特性**: 关联项多边界、增强的高阶生命周期、改进的自动特征推断
//! - **标准库**: NonZero::div_ceil、rotate_right 等
//! - **性能优化**: 迭代器方法特化、泛型约束优化
//!
//! ### 迁移建议
//!
//! 1. 更新 Cargo.toml: `rust-version = "1.92"`
//! 2. 参考 `rust_192_features.rs` 了解最新特性
//! 3. 查看 `docs/RUST_192_GENERIC_IMPROVEMENTS.md` 了解完整改进
//!
//! 参考:
//! - [Rust 1.92.0 Release Notes](https://releases.rs/docs/1.92.0/)
//! - [历史版本: Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
//!
//! ---
//!
//! # Rust 1.89 相关语言能力在泛型方向的重要对齐点（精选）
//!
//! 1) TAIT（Type Alias Impl Trait，稳定的 impl Trait 类型别名用法）
//!    - 用途：为复杂的 `impl Trait` 返回或迭代器等零成本抽象提供可命名的别名。
//!
//! 2) RPITIT（return-position impl Trait in traits，在 trait 方法返回位置使用 impl Trait）
//!    - 用途：在 trait 方法签名中直接返回 `impl Trait`，配合对象安全限制或使用 GAT 进行更强抽象。
//!
//! 3) Const generics（常量泛型，含更完整的表达能力）
//!    - 用途：在类型层面对大小/阈值等不变参数建模，生成零成本特化代码。
//!
//! 下方示例均保持最小可编译与直观演示。更多边界与高级用法建议参考标准库与成熟库实现（如 itertools、rayon、serde）。

// 1) TAIT（退而求其次演示）：
// 由于某些编译器通道/版本下“类型别名中的 impl Trait”可能受限，这里以
// “函数返回位置 impl Trait”来表达与 TAIT 接近的意图（零成本迭代器组合）。
pub mod tait_like {
    pub fn map_then_filter<'a, T, I, F, P>(
        iter: I,
        map_fn: F,
        pred: P,
    ) -> impl Iterator<Item = T> + 'a
    where
        I: IntoIterator + 'a,
        F: Fn(I::Item) -> T + 'a,
        P: Fn(&T) -> bool + 'a,
    {
        iter.into_iter().map(map_fn).filter(pred)
    }

    #[cfg(test)]
    mod tests {
        #[test]
        fn test_map_then_filter() {
            let data = vec![1, 2, 3, 4, 5];
            let it = super::map_then_filter(data, |x| x * 2, |x| *x > 5);
            let out: Vec<_> = it.collect();
            assert_eq!(out, vec![6, 8, 10]);
        }
    }
}

// 2) RPITIT: 在 trait 方法返回位置使用 impl Trait
pub mod rpitit {
    pub trait MakeIter {
        // 返回位置 impl Trait
        fn make_iter(&self) -> impl Iterator<Item = i32>;
    }

    pub struct RangeMaker {
        pub start: i32,
        pub end: i32,
    }

    impl MakeIter for RangeMaker {
        fn make_iter(&self) -> impl Iterator<Item = i32> {
            (self.start..self.end).map(|x| x * 2)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        fn test_rpitit_basic() {
            let m = RangeMaker { start: 1, end: 5 };
            let v: Vec<i32> = m.make_iter().collect();
            assert_eq!(v, vec![2, 4, 6, 8]);
        }
    }
}

// 3) Const generics：常量泛型数组/向量包装与边界
pub mod const_generics {
    // 固定容量环形缓冲区（最小可用示例）
    pub struct RingBuffer<T, const N: usize> {
        data: [Option<T>; N],
        head: usize,
        len: usize,
    }

    impl<T, const N: usize> Default for RingBuffer<T, N> {
        fn default() -> Self {
            Self::new()
        }
    }

    impl<T, const N: usize> RingBuffer<T, N> {
        pub fn new() -> Self {
            // 使用数组初始化需要 Copy/Clone；这里用 Option::None; N>0 时可工作
            Self {
                data: std::array::from_fn(|_| None),
                head: 0,
                len: 0,
            }
        }

        pub fn capacity(&self) -> usize {
            N
        }
        pub fn len(&self) -> usize {
            self.len
        }
        pub fn is_empty(&self) -> bool {
            self.len == 0
        }
        pub fn is_full(&self) -> bool {
            self.len == N
        }

        pub fn push(&mut self, item: T) -> Result<(), T> {
            if self.is_full() {
                return Err(item);
            }
            let idx = (self.head + self.len) % N;
            self.data[idx] = Some(item);
            self.len += 1;
            Ok(())
        }

        pub fn pop(&mut self) -> Option<T> {
            if self.is_empty() {
                return None;
            }
            let idx = self.head;
            self.head = (self.head + 1) % N;
            self.len -= 1;
            self.data[idx].take()
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        fn test_ring_buffer() {
            let mut rb: RingBuffer<i32, 4> = RingBuffer::new();
            assert!(rb.is_empty());
            assert_eq!(rb.capacity(), 4);
            rb.push(1).unwrap();
            rb.push(2).unwrap();
            rb.push(3).unwrap();
            assert_eq!(rb.len(), 3);
            assert_eq!(rb.pop(), Some(1));
            assert_eq!(rb.pop(), Some(2));
            assert_eq!(rb.pop(), Some(3));
            assert_eq!(rb.pop(), None);
        }
    }
}

// 汇总演示入口，便于在 bin/main 中调用
pub fn demonstrate_rust_189_generics() {
    // TAIT-like
    {
        let data = [1, 2, 3, 4, 5];
        let out: Vec<_> =
            crate::rust_189_features::tait_like::map_then_filter(&data, |x| x * 3, |x| *x % 2 == 0)
                .collect();
        println!("TAIT-like out: {:?}", out);
    }

    // RPITIT
    {
        use crate::rust_189_features::rpitit::{MakeIter, RangeMaker};
        let maker = RangeMaker { start: 0, end: 4 };
        let v: Vec<_> = maker.make_iter().collect();
        println!("RPITIT out: {:?}", v);
    }

    // Const generics
    {
        let mut rb: const_generics::RingBuffer<&str, 3> = const_generics::RingBuffer::new();
        let _ = rb.push("a");
        let _ = rb.push("b");
        let _ = rb.push("c");
        println!("ConstGenerics len={} full={}", rb.len(), rb.is_full());
        println!("pop1={:?} pop2={:?}", rb.pop(), rb.pop());
    }
}
