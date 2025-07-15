// 类型系统案例：基本类型推导与检查
// 理论映射：对应“类型判断”与“类型安全性”定理（见 01_formal_type_system.md 附录）

fn main() {
    let x: i32 = 42; // x 的类型由声明推导为 i32
    let y = x + 1;   // y 的类型由上下文自动推导为 i32
    // let z: String = x; // 编译错误，类型不兼容，类型安全性保证
    println!("x = {}, y = {}", x, y);
} 