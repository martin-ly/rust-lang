// 生命周期案例：静态生命周期
// 理论映射：对应“静态生命周期”与“生命周期包含关系”理论（见 02_lifetime_and_scope.md 附录）

fn print_static(s: &'static str) {
    println!("静态字符串: {}", s);
}

fn main() {
    let s: &'static str = "hello, world";
    print_static(s);
} 