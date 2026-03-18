//! 声明宏（Macro Rules）
//!
//! 声明宏是Rust中最基础的宏形式，使用macro_rules!定义。

/// 基础示例：创建一个简单的vec!宏等价物
#[macro_export]
macro_rules! my_vec {
    // 匹配逗号分隔的表达式
    ($($x:expr),*) => {
        {
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            temp_vec
        }
    };
}

/// 带有重复模式的宏 - 计算token数量
#[macro_export]
macro_rules! count_tokens {
    // 计算参数数量
    () => { 0 };
    ($single:tt) => { 1 };
    ($first:tt $($rest:tt)*) => {
        1 + count_tokens!($($rest)*)
    };
}

/// 实现类似vec!的带容量初始化
#[macro_export]
macro_rules! my_vec_with_capacity {
    // 匹配vec![value; count]格式
    ($elem:expr; $n:expr) => {
        {
            let mut temp_vec = Vec::with_capacity($n);
            for _ in 0..$n {
                temp_vec.push($elem.clone());
            }
            temp_vec
        }
    };
}

/// 条件编译宏示例
#[macro_export]
macro_rules! debug_print {
    // 只在debug模式下打印
    ($($arg:tt)*) => {
        #[cfg(debug_assertions)]
        {
            println!($($arg)*);
        }
    };
}

/// 实现自定义的if let链式调用
#[macro_export]
macro_rules! if_let_chain {
    // 基础情况：只有表达式
    ($e:expr) => { $e };
    // 递归情况：let绑定和剩余表达式
    (let $pat:pat = $expr:expr, $($rest:tt)*) => {
        if let $pat = $expr {
            if_let_chain!($($rest)*)
        } else {
            None
        }
    };
    // 最终表达式
    ($e:expr $(,)?) => { Some($e) };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_my_vec() {
        let v = my_vec![1, 2, 3];
        assert_eq!(v, vec![1, 2, 3]);
    }

    #[test]
    fn test_my_vec_with_capacity() {
        let v = my_vec_with_capacity![0; 5];
        assert_eq!(v, vec![0, 0, 0, 0, 0]);
        assert_eq!(v.capacity(), 5);
    }

    #[test]
    fn test_count_macro() {
        assert_eq!(count_tokens!(), 0);
        assert_eq!(count_tokens!(a), 1);
        assert_eq!(count_tokens!(a b c), 3);
    }
}
