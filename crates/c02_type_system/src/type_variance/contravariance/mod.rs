//! 逆变（contravariance）：子类型关系在函数参数位置被反转。

pub mod define;

/// 期望一个能处理 `'static` 引用的函数指针。
pub fn use_static_handler(handler: fn(&'static str)) {
    let s: &'static str = "hello";
    handler(s);
}

/// 这个函数可以接受任何生命周期的 `&str`，因此它的类型是 `fn(&'static str)` 的子类型。
pub fn elided_handler(_s: &str) {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn contravariant_function_pointer() {
        // `fn(&str)`（即 `for<'a> fn(&'a str)`）可以赋值给 `fn(&'static str)`
        use_static_handler(elided_handler);
    }
}
