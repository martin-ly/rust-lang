//! 型变示例：协变、不变与逆变。

use std::cell::Cell;

/// 协变：`'static` 可缩短为任意 `'a`。
fn covariance<'a>(s: &'static str) -> &'a str {
    s
}

/// 逆变：函数参数位置子类型关系被反转。
fn contravariance_example() {
    fn expect_static(_: fn(&'static str)) {}
    fn accepts_any(_: &str) {}

    // `fn(&str)` 是 `fn(&'static str)` 的子类型。
    expect_static(accepts_any);
}

/// 不变：`Cell<T>` 不允许随 `T` 的子类型化。
fn invariance_example() {
    let c = Cell::new("static");
    let local = String::from("local");
    c.set(&local);
    println!("cell value after set: {}", c.get());
}

fn main() {
    let s = covariance("hello covariance");
    println!("{s}");

    contravariance_example();
    invariance_example();

    // 容器协变示例
    let b: Box<&'static str> = Box::new("boxed static");
    let b_any: Box<&str> = b;
    println!("boxed: {}", b_any);
}
