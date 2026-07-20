// 所有权案例：所有权转移与移动语义
// 理论映射：对应“所有权转移”与“所有权唯一性”定理（见 01_formal_ownership_system.md 附录）

fn main() {
    let s1 = String::from("hello");
    let s2 = s1; // 所有权从s1转移到s2，s1失效
    // println!("{}", s1); // 编译错误，s1已无所有权
    println!("{}", s2);
} 