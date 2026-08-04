// 内存管理案例：内存泄漏检测与可达性
// 理论映射：对应“内存泄漏检测”定理（见 01_formal_memory_model.md 附录）

use std::rc::Rc;

fn main() {
    let a = Rc::new(1);
    let b = Rc::clone(&a);
    println!("a = {}, b = {}", a, b);
    // Rc计数为2，a和b都离开作用域后内存被释放，无泄漏
    // 若循环引用则会导致内存泄漏
} 