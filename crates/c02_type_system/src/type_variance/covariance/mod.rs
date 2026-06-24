//! 协变（covariance）：子类型关系在泛型构造器中被保持。

/// 生命周期协变：`'static` 可缩短为任意 `'a`。
pub fn static_to_any<'a>() -> &'a str {
    let s: &'static str = "static";
    s
}

/// `Box<T>` 对 `T` 协变：可将 `Box<&'static str>` 传给需要 `Box<&'a str>` 的位置。
pub fn box_covariance<'a>(b: Box<&'static str>) -> Box<&'a str> {
    b
}

/// `Option<T>` 对 `T` 协变。
pub fn option_covariance<'a>(o: Option<&'static str>) -> Option<&'a str> {
    o
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lifetime_covariance() {
        assert_eq!(static_to_any(), "static");
    }

    #[test]
    fn box_and_option_covariance() {
        let b: Box<&'static str> = Box::new("boxed");
        let b_any: Box<&str> = box_covariance(b);
        assert_eq!(*b_any, "boxed");

        let o: Option<&'static str> = Some("optional");
        let o_any: Option<&str> = option_covariance(o);
        assert_eq!(o_any, Some("optional"));
    }
}
