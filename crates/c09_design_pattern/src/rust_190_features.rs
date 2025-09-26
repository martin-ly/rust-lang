//! Rust 1.90 / Edition 2024 特性示例入口

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


