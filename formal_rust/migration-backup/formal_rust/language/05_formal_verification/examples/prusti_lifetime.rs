// Prusti生命周期与借用安全性验证示例
// 工程意义：演示如何用Prusti注解验证生命周期与借用安全，防止悬垂指针
use prusti_contracts::*;

#[requires(x.len() > 0)]
#[ensures(result == x[0])]
fn first<'a>(x: &'a [i32]) -> i32 {
    x[0]
}

fn main() {
    let arr = vec![10, 20, 30];
    let f = first(&arr);
    assert_eq!(f, 10);
}

// 形式化注释：
// ∀x: &'a [i32], x.len() > 0 ⇒ first(x) == x[0], 且result的生命周期≤'a
// 工具建议：Prusti可自动验证生命周期与借用安全 