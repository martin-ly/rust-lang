//! 子类型关系：生命周期子类型化与 trait bound 多态。

/// 动物 trait。
pub trait Animal {
    /// 发出声音。
    fn speak(&self) -> &'static str;
}

/// 狗。
pub struct Dog;

impl Animal for Dog {
    fn speak(&self) -> &'static str {
        "Woof"
    }
}

/// 猫。
pub struct Cat;

impl Animal for Cat {
    fn speak(&self) -> &'static str {
        "Meow"
    }
}

/// 任何实现 [`Animal`] 的类型都可以传入。
pub fn make_sound<T: Animal>(animal: T) -> &'static str {
    animal.speak()
}

/// `'static` 生命周期是任何生命周期的子类型，因此可以缩短。
pub fn shorten_lifetime<'a>(s: &'static str) -> &'a str {
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trait_bound_subtyping() {
        assert_eq!(make_sound(Dog), "Woof");
        assert_eq!(make_sound(Cat), "Meow");
    }

    #[test]
    fn test_lifetime_subtyping() {
        let s: &'static str = "static string";
        assert_eq!(shorten_lifetime(s), "static string");
    }
}
