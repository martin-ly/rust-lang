//! 示例：在算法库中使用 Rust 2024 / Rust 1.90 成熟语法

use c08_algorithms::algorithms::rust_2024_features as f24;

fn main() {
    // let-else
    let data = vec![10, 20, 30];
    let first = f24::first_or_error(&data).expect("has first");
    println!("first = {}", first);

    // try 块
    let sum = f24::sum_three_try(Ok(1), Ok(2), Ok(3)).expect("ok");
    println!("sum = {}", sum);

    // is_some_and
    println!("has_even(Some(4)) = {}", f24::has_even(Some(4)));

    // 返回位置 impl Iterator
    let evens: Vec<_> = f24::range_even_iter(0, 10).collect();
    println!("evens = {:?}", evens);
}


