// 泛型案例：单态化与泛型实例化
// 理论映射：对应“单态化一致性”定理（见 01_formal_generics_system.md 附录）

fn add<T: std::ops::Add<Output = T>>(a: T, b: T) -> T {
    a + b
}

fn main() {
    let x = add(1, 2); // 实例化为i32
    let y = add(1.5, 2.5); // 实例化为f64
    println!("x = {}, y = {}", x, y);
} 