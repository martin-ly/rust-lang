//! Rust 1.90 / Edition 2024 特性示例入口 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features.rs`

pub mod highlights {
    /// 展示 never 类型在不可达终止函数中的使用
    #[allow(unused)]
    pub fn terminate_with_panic() -> ! {
        panic!("terminated")
    }

    /// 展示 if-let 链式匹配
    #[allow(unused)]
    pub fn if_let_chain(opt_a: Option<i32>, opt_b: Option<i32>) -> Option<i32> {
        if let Some(a) = opt_a && let Some(b) = opt_b {
            Some(a + b)
        } else {
            None
        }
    }
}

/// GATs（泛型关联类型）示例：带借用生命周期的集合访问
pub mod gats_demo {
    /// 定义一个集合视图 trait，返回值依赖输入生命周期
    pub trait CollectionView {
        type Item<'a>
        where
            Self: 'a;

        fn get<'a>(&'a self, index: usize) -> Option<Self::Item<'a>>;
    }

    impl<T> CollectionView for Vec<T> {
        type Item<'a> = &'a T where Self: 'a;

        fn get<'a>(&'a self, index: usize) -> Option<Self::Item<'a>> {
            self.as_slice().get(index)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_gats_vec_view() {
            let data = vec![10, 20, 30];
            let v = <Vec<i32> as CollectionView>::get(&data, 1).copied();
            assert_eq!(v, Some(20));
        }
    }
}

/// RPITIT（在 trait 方法中返回 impl Trait）示例
pub mod rpitit_demo {
    /// 文本源：提供按词迭代视图
    pub trait TextSource {
        /// 在 trait 方法中返回位置 impl Iterator（RPITIT）
        fn words<'a>(&'a self) -> impl Iterator<Item = &'a str> + 'a;
    }

    impl TextSource for String {
        fn words<'a>(&'a self) -> impl Iterator<Item = &'a str> + 'a {
            self.split_whitespace()
        }
    }

    impl TextSource for &str {
        fn words<'a>(&'a self) -> impl Iterator<Item = &'a str> + 'a {
            self.split_whitespace()
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_words_on_string() {
            let s = String::from("hello rust 190");
            let v: Vec<&str> = TextSource::words(&s).collect();
            assert_eq!(v, vec!["hello", "rust", "190"]);
        }

        #[test]
        fn test_words_on_str() {
            let s: &str = "a b c";
            let mut it = TextSource::words(&s);
            assert_eq!(it.next(), Some("a"));
            assert_eq!(it.next(), Some("b"));
            assert_eq!(it.next(), Some("c"));
            assert_eq!(it.next(), None);
        }
    }
}

/// dyn upcasting（子 trait 到父 trait 的动态上行转型）示例
pub mod dyn_upcasting_demo {
    pub trait Logger {
        fn log(&self, msg: &str) -> String;
    }

    pub trait TimestampLogger: Logger {
        fn now(&self) -> &'static str;
    }

    pub struct SimpleTs;

    impl Logger for SimpleTs {
        fn log(&self, msg: &str) -> String { format!("[{}] {}", self.now(), msg) }
    }

    impl TimestampLogger for SimpleTs {
        fn now(&self) -> &'static str { "2025-09-26T00:00:00Z" }
    }

    #[allow(dead_code)]
    fn take_logger(_l: &mut dyn Logger) {}

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_dyn_upcast() {
            let mut ts: Box<dyn TimestampLogger> = Box::new(SimpleTs);
            // 1.82+ 支持：&mut dyn Sub -> &mut dyn Super 的隐式上转型
            take_logger(ts.as_mut());
            assert!(ts.log("x").contains("x"));
        }
    }
}
