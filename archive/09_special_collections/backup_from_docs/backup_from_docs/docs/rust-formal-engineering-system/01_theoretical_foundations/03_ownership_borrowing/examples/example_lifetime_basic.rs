// 生命周期案例：基础生命周期约束
// 理论映射：对应“生命周期包含关系”与“生命周期推导正确性”定理（见 02_lifetime_and_scope.md 附录）

fn main() {
    let s1 = String::from("hello");
    let r = &s1; // r 的生命周期被自动推断为不短于 s1
    println!("{}", r);
} 