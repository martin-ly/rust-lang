// 类型系统案例：泛型与多态类型推导
// 理论映射：对应“多态性”“泛型”理论（见 01_formal_type_system.md 附录）

fn identity<T>(x: T) -> T {
    x
}

fn main() {
    let a = identity(5);      // T = i32
    let b = identity("hi"); // T = &str
    println!("a = {}, b = {}", a, b);
} 