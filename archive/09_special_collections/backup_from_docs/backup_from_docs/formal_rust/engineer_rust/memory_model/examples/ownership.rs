// 所有权与借用示例 Ownership & Borrowing Example
fn main() {
    let s = String::from("hello");
    let r = &s; // 不可变借用
    println!("{} {}", s, r);
} 