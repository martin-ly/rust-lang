/*
Rust 1.89 方向的 GAT（Generic Associated Types）与 HRTB（Higher-Rank Trait Bounds）精简演示。

GAT 用于在关联类型中引入额外的生命周期/类型参数，使 trait 的接口表达力更强。
HRTB 用于像 `for<'a> ...` 这类“对所有生命周期均成立”的约束，常见于函数指针/闭包接收借用数据的情况。
*/

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
        pub fn new(data: Vec<T>) -> Self { Self { data } }
    }

    impl<T> SliceProvider for VecProvider<T> {
        type Item<'a> = &'a T where Self: 'a;

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
