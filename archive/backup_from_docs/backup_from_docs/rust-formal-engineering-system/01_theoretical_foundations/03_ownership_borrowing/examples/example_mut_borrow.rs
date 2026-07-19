// 所有权案例：可变借用与借用冲突
// 理论映射：对应“可变借用”与“借用安全性”定理（见 01_formal_ownership_system.md 附录）

fn main() {
    let mut s = String::from("rust");
    let r1 = &mut s; // 可变借用，独占
    r1.push_str(" ownership");
    // let r2 = &s; // 编译错误，可变借用期间不可再有不可变借用
    println!("{}", r1);
} 