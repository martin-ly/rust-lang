// 泛型案例：Trait约束与泛型安全
// 理论映射：对应“Trait约束”与“泛型类型安全性”定理（见 01_formal_generics_system.md 附录）

fn print_debug<T: std::fmt::Debug>(x: T) {
    println!("{:?}", x);
}

fn main() {
    print_debug(123);
    print_debug("hello");
} 