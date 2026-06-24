//! Newtype 模式示例：为单位和 ID 提供类型安全。

use c02_type_system::type_operation::newtype::{Identifier, ProductId, UserId};

fn main() {
    let user = UserId(42);
    let product = ProductId(42);

    println!("user: {user} (namespace: {})", UserId::namespace());
    println!(
        "product: {product:?} (namespace: {})",
        ProductId::namespace()
    );

    // 底层值相同，但类型不同，无法直接混用。
    assert_eq!(user.0, product.0);
}
