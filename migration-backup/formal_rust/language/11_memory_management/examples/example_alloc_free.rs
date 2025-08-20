// 内存管理案例：内存分配与释放
// 理论映射：对应“分配与释放操作”与“内存安全性”定理（见 01_formal_memory_model.md 附录）

fn main() {
    let v = Box::new(42); // 分配内存
    println!("v = {}", v);
    // v 离开作用域时自动释放内存
} 