//! Newtype 模式：通过单字段结构体提供类型安全、语义清晰与 orphan rule 规避。

use std::fmt;

/// 用户 ID Newtype。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UserId(pub u32);

/// 产品 ID Newtype。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProductId(pub u32);

impl fmt::Display for UserId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "U{}", self.0)
    }
}

/// 自定义标识符 trait，用 Newtype 为外部/原始类型实现本地 trait。
pub trait Identifier {
    /// 返回命名空间。
    fn namespace() -> &'static str;
}

impl Identifier for UserId {
    fn namespace() -> &'static str {
        "user"
    }
}

impl Identifier for ProductId {
    fn namespace() -> &'static str {
        "product"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn newtypes_are_distinct() {
        let user = UserId(1);
        let product = ProductId(1);

        // 底层值相同，但类型不同，无法直接混用。
        assert_eq!(user.0, product.0);
        assert_eq!(user.to_string(), "U1");
    }

    #[test]
    fn newtype_implements_local_trait() {
        assert_eq!(UserId::namespace(), "user");
        assert_eq!(ProductId::namespace(), "product");
    }
}
