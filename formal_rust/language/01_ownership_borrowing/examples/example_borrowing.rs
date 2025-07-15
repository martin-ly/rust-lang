// 所有权案例：借用规则与生命周期
// 理论映射：对应“借用规则”与“借用安全性”定理（见 01_formal_ownership_system.md 附录）

fn main() {
    let s = String::from("world");
    let r = &s; // 不可变借用
    println!("{}", r);
    // s 生命周期覆盖 r，借用安全
} 