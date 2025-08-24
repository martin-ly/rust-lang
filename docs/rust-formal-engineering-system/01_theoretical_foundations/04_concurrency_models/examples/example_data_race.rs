// 并发案例：数据竞争检测与防护
// 理论映射：对应“数据竞争”与“无数据竞争”定理（见 01_formal_concurrency_model.md 附录）

// 本例演示Rust类型系统如何防止数据竞争
use std::thread;

fn main() {
    let mut data = 0;
    // let r1 = &mut data;
    // let r2 = &mut data; // 编译错误：同一时刻只能有一个可变引用，防止数据竞争
    // thread::spawn(move || { *r1 += 1; });
    // thread::spawn(move || { *r2 += 1; });
    // Rust类型系统和借用检查器在编译期阻止了数据竞争
    println!("数据竞争被静态阻止，data = {}", data);
} 