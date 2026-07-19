// 泛型案例：泛型函数与类型参数
// 理论映射：对应“泛型类型表达式”与“泛型类型安全性”定理（见 01_formal_generics_system.md 附录）

fn identity<T>(x: T) -> T {
    x
}

fn main() {
    let a = identity(42);
    let b = identity("hello");
    println!("a = {}, b = {}", a, b);
} 