//! # Rust 1.89 特性示例 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features.rs`
//!
//! ## 版本历史说明
//!
//! 本文件展示 Rust 1.89 版本的 GAT 和 HRTB 特性，当前项目已升级到 Rust 1.92.0。
//!
//! ### Rust 1.92.0 主要改进
//!
//! - **关联项多边界**: 更灵活的类型约束表达
//! - **高阶生命周期增强**: 更精确的生命周期处理
//! - **标准库**: NonZero::div_ceil、rotate_right 等
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
//! # Rust 1.89 方向的 GAT（Generic Associated Types）与 HRTB（Higher-Rank Trait Bounds）精简演示
//!
//! GAT 用于在关联类型中引入额外的生命周期/类型参数，使 trait 的接口表达力更强。
//! HRTB 用于像 `for<'a> ...` 这类"对所有生命周期均成立"的约束，常见于函数指针/闭包接收借用数据的情况。


// 1) GAT：一个最简“只读切片访问器”接口
pub mod gat_demo {
    pub trait SliceProvider {
        type Item<'a>
        where
            Self: 'a;

        fn get<'a>(&'a self, idx: usize) -> Option<Self::Item<'a>>;
    }

    pub struct VecProvider<T> {
        pub data: Vec<T>,
    }

    impl<T> VecProvider<T> {
        pub fn new(data: Vec<T>) -> Self {
            Self { data }
        }
    }

    impl<T> SliceProvider for VecProvider<T> {
        type Item<'a>
            = &'a T
        where
            Self: 'a;

        fn get<'a>(&'a self, idx: usize) -> Option<Self::Item<'a>> {
            self.data.get(idx)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_gat_slice_provider() {
            let p = VecProvider::new(vec![10, 20, 30]);
            assert_eq!(p.get(1), Some(&20));
            assert_eq!(p.get(3), None);
        }
    }
}

// 2) HRTB：for<'a> 约束的闭包/函数示例
pub mod hrtb_demo {
    // 要求传入的转换函数对所有生命周期都有效
    pub fn map_all<'b, F>(input: &'b str, f: F) -> String
    where
        F: for<'a> Fn(&'a str) -> &'a str,
    {
        f(input).to_string()
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_hrtb_map_all() {
            let s = String::from("hello");
            // 身份函数对任意借用生命周期都可用
            let out = map_all(&s, |x| x);
            assert_eq!(out, "hello");
        }
    }
}

pub fn demonstrate_gat_hrtb() {
    use gat_demo::{SliceProvider, VecProvider};

    let p = VecProvider::new(vec![1, 2, 3]);
    println!("GAT get(0)={:?}", p.get(0));

    let s = String::from("HRTB");
    let r = hrtb_demo::map_all(&s, |x| x);
    println!("HRTB map_all -> {}", r);
}
