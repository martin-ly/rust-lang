// Creusot循环不变式与归纳证明示例
// 工程意义：演示如何用Creusot注解和逻辑函数验证循环不变式与归纳性质
use creusot_contracts::*;

#[logic]
fn sum_range(a: Int, b: Int) -> Int {
    if a >= b { 0 } else { a + sum_range(a + 1, b) }
}

#[requires(a <= b)]
#[ensures(result == sum_range(a@, b@))]
fn sum_range_iter(a: i32, b: i32) -> i32 {
    let mut sum = 0;
    let mut i = a;
    while i < b {
        invariant![a <= i && i <= b && sum + sum_range(i.into(), b.into()) == sum_range(a.into(), b.into())];
        sum += i;
        i += 1;
    }
    sum
}

fn main() {
    let s = sum_range_iter(1, 5);
    assert_eq!(s, 10);
}

// 形式化注释：
// 循环不变式：sum + sum_range(i, b) == sum_range(a, b)
// 工具建议：Creusot可自动验证归纳不变式 