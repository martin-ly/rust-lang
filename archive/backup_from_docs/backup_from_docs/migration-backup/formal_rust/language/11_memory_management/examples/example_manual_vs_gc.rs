// 内存管理案例：手动管理与垃圾回收对比
// 理论映射：对应“手动管理”与“垃圾回收”理论（见 01_formal_memory_model.md 附录）

fn manual_management() {
    let v = Box::new(100);
    println!("手动管理: {}", v);
    // Rust作用域结束自动释放，等价于手动free
}

fn gc_simulation() {
    use std::rc::Rc;
    let a = Rc::new(200);
    let b = Rc::clone(&a);
    println!("GC模拟: a = {}, b = {}", a, b);
    // Rc计数为2，所有引用离开作用域后自动释放
}

fn main() {
    manual_management();
    gc_simulation();
} 