//! 基础类型示例：标量、复合、引用与切片。

fn main() {
    // 标量类型
    let n: i32 = 42;
    let f: f64 = std::f64::consts::PI;
    let b: bool = true;
    let c: char = '中';

    // 复合类型
    let arr: [i32; 3] = [1, 2, 3];
    let tuple: (i32, f64, &str) = (1, 2.0, "hello");

    // 引用与切片
    let slice: &[i32] = &arr;
    let s: &str = "Rust";

    println!("scalar: n={n}, f={f}, b={b}, c={c}");
    println!("compound: arr={arr:?}, tuple={tuple:?}");
    println!("reference: slice={slice:?}, s={s}");
}
