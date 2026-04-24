//! # 练习 1: 声明宏
//!
//! **难度**: Medium  
//! **考点**: macro_rules!、重复模式、递归宏
//!
//! ## 题目描述
//!
//! 编写实用的声明宏，简化常见代码模式。

/// 类似 vec!，但创建 HashSet
#[macro_export]
macro_rules! set {
    ($($item:expr),* $(,)?) => {{
        #[allow(unused_mut)]
        let mut s = ::std::collections::HashSet::new();
        $(s.insert($item);)*
        s
    }};
}

/// 便捷创建 Result::Ok 或返回 Err
#[macro_export]
macro_rules! ok_or_return {
    ($expr:expr) => {
        match $expr {
            ::std::result::Result::Ok(v) => v,
            ::std::result::Result::Err(e) => return ::std::result::Result::Err(e),
        }
    };
}

/// 测量代码块执行时间
#[macro_export]
macro_rules! timed {
    ($name:expr, $block:block) => {{
        let start = ::std::time::Instant::now();
        let result = $block;
        let elapsed = start.elapsed();
        println!("[{}] 耗时: {:?}", $name, elapsed);
        result
    }};
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    #[test]
    fn test_set_macro() {
        let s: HashSet<i32> = set![1, 2, 3];
        assert_eq!(s.len(), 3);
        assert!(s.contains(&1));
    }

    #[test]
    fn test_set_macro_empty() {
        let s: HashSet<i32> = set![];
        assert!(s.is_empty());
    }

    #[test]
    fn test_ok_or_return() {
        fn demo(x: Result<i32, &str>) -> Result<i32, &str> {
            let v = ok_or_return!(x);
            Ok(v * 2)
        }
        assert_eq!(demo(Ok(5)), Ok(10));
        assert_eq!(demo(Err("fail")), Err("fail"));
    }

    #[test]
    fn test_timed_macro() {
        let result = timed!("test", {
            let mut sum = 0;
            for i in 0..100 {
                sum += i;
            }
            sum
        });
        assert_eq!(result, 4950);
    }
}
