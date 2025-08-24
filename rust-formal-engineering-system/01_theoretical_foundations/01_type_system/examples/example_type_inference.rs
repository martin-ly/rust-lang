// 类型系统案例：类型推导算法演示
// 理论映射：对应“类型推导”与“类型推导算法正确性”定理（见 01_formal_type_system.md 附录）

fn add<T: std::ops::Add<Output = T>>(a: T, b: T) -> T {
    a + b
}

fn main() {
    let x = 1;
    let y = 2;
    let z = add(x, y); // 类型推导：T = i32
    println!("z = {}", z);

    let s1 = String::from("foo");
    let s2 = String::from("bar");
    let s3 = add(s1, s2); // 类型推导：T = String
    println!("s3 = {}", s3);
} 