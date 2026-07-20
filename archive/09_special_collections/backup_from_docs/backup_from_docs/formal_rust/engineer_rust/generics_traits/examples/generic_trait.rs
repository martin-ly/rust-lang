// 泛型与Trait示例 Generic & Trait Example
fn add<T: std::ops::Add<Output = T>>(a: T, b: T) -> T { a + b }

trait Printable {
    fn print(&self);
}

impl Printable for i32 {
    fn print(&self) { println!("i32: {}", self); }
}

fn main() {
    let x = add(1, 2);
    x.print();
} 