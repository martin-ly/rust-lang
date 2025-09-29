// Creusot trait不变式与接口安全性验证示例
// 工程意义：演示如何用Creusot注解验证trait实现的接口不变式，适用于高阶trait安全性建模
use creusot_contracts::*;

trait Bounded {
    fn min(&self) -> i32;
    fn max(&self) -> i32;
}

struct Range {
    lo: i32,
    hi: i32,
}

impl Bounded for Range {
    #[logic]
    fn min(&self) -> i32 { self.lo }
    #[logic]
    fn max(&self) -> i32 { self.hi }
}

#[requires(r.min() <= r.max())]
#[ensures(result >= r.min() && result <= r.max())]
fn clamp<T: Bounded>(r: &T, x: i32) -> i32 {
    if x < r.min() { r.min() }
    else if x > r.max() { r.max() }
    else { x }
}

fn main() {
    let r = Range { lo: 0, hi: 10 };
    assert_eq!(clamp(&r, 5), 5);
    assert_eq!(clamp(&r, -3), 0);
    assert_eq!(clamp(&r, 20), 10);
}

// 形式化注释：
// ∀T: Bounded, ∀r: &T, r.min() ≤ r.max() ⇒ clamp(r, x) ∈ [r.min(), r.max()]
// 工具建议：Creusot可自动验证trait接口不变式 