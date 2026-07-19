// Creusot高阶验证示例
// 工程意义：演示如何用Creusot验证高阶函数与复杂不变式
use creusot_contracts::*;

#[logic]
fn is_sorted(v: &Vec<i32>) -> bool {
    v.windows(2).all(|w| w[0] <= w[1])
}

#[ensures(is_sorted(&result))]
fn sorting_property(mut v: Vec<i32>) -> Vec<i32> {
    v.sort();
    v
} 