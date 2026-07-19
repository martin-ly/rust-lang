// Prusti自动化验证注解示例
// 工程意义：演示如何用Prusti注解静态验证前置/后置条件
use prusti_contracts::*;

#[requires(n >= 0)]
#[ensures(result >= n)]
fn increment(n: i32) -> i32 {
    n + 1
}

fn main() {
    let x = increment(5);
    assert!(x >= 5);
} 