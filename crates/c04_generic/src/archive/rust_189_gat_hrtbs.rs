//! # Rust 1.89 特性示例 (历史版本)
//! # Rust 1.89 feature example (this )
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//! ⚠️ **this ** - this as reference
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features.rs`
//! **when before this **: Rust 1.92.0+ | feature reference `rust_192_features.rs`
//! ## 版本历史说明
//! ## this explain
//! ### Rust 1.92.0 主要改进
//! ### Rust 1.92.0 main
//! - **关联项多边界**: 更灵活的类型约束表达
//! - **edge **: type express
//! - **高阶生命周期增强**: 更精确的生命周期处理
//! - **lifetime **: lifetime
//! ### 迁移建议
//! ###
//! 1. 更新 Cargo.toml: `rust-version = "1.92"`
//! 参考:
//! reference :
//! - [历史版本: Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
//! - [历史版this: Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
//!
//! # Rust 1.89 direction GAT（Generic Associated Types）and HRTB（Higher-Rank Trait Bounds）精简Demonstration of
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
