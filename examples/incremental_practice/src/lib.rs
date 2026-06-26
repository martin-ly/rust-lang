//! 用于观测 rustc 增量编译的最小 crate。
//!
//! 模块划分 intentionally 简单：
//! - `math`：纯计算函数
//! - `greet`：字符串函数
//! - `analyze`：组合前两者
//!
//! 修改其中一个函数后重新编译，可在 `-Z incremental-info` 输出中看到
//! 仅受影响节点被标记 dirty，其余节点被复用。

pub mod math {
    /// 两数相加。
    #[must_use]
    pub fn add(a: i32, b: i32) -> i32 {
        a + b
    }

    /// 两数相乘。
    #[must_use]
    pub fn mul(a: i32, b: i32) -> i32 {
        a * b
    }
}

pub mod greet {
    /// 返回问候语。
    #[must_use]
    pub fn hello(name: &str) -> String {
        format!("Hello, {name}!")
    }
}

pub mod analyze {
    use super::{greet, math};

    /// 对一个数值做简单分析：先乘后加，再生成报告。
    #[must_use]
    pub fn report(x: i32, y: i32, name: &str) -> String {
        let value = math::mul(x, y);
        let value = math::add(value, 1);
        let greeting = greet::hello(name);
        format!("{greeting} The result is {value}.")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn math_basic() {
        assert_eq!(math::add(2, 3), 5);
        assert_eq!(math::mul(4, 5), 20);
    }

    #[test]
    fn greet_basic() {
        assert_eq!(greet::hello("Rust"), "Hello, Rust!");
    }

    #[test]
    fn report_basic() {
        assert_eq!(
            analyze::report(3, 4, "World"),
            "Hello, World! The result is 13."
        );
    }
}
