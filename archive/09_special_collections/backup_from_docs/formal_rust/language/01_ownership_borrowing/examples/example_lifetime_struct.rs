// 生命周期案例：结构体生命周期标注
// 理论映射：对应“生命周期参数”与“生命周期推导”理论（见 02_lifetime_and_scope.md 附录）

struct Book<'a> {
    title: &'a str,
}

fn main() {
    let s = String::from("Rust Book");
    let book = Book { title: &s };
    println!("书名: {}", book.title);
} 