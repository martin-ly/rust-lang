//! # Rust 1.92.0 Box::new_zeroed 和 Box::new_zeroed_slice 演示
//!
//! 本示例展示 Rust 1.92.0 中新增的零初始化内存分配方法：
//! - `Box::new_zeroed()` - 零初始化单个值
//! - `Box::new_zeroed_slice()` - 零初始化切片
//! - `Rc::new_zeroed()` / `Arc::new_zeroed()` - 引用计数的零初始化
//!
//! ## Rust 1.92.0 新特性
//!
//! 这些方法类似于 C 语言的 `calloc`，在堆上分配内存并进行零初始化。
//! 返回 `Box<MaybeUninit<T>>`，需要使用 `assume_init()` 来获取实际值。

use std::mem::MaybeUninit;

/// 演示 Box::new_zeroed 的使用
fn demonstrate_box_new_zeroed() {
    println!("=== Box::new_zeroed 演示 ===");

    // Rust 1.92.0: 创建零初始化的 Box
    // 返回 Box<MaybeUninit<i32>>，内存被零初始化
    let zeroed_box: Box<MaybeUninit<i32>> = Box::new_zeroed();

    // 使用 unsafe assume_init() 获取值（因为我们已经知道内存是零初始化的）
    unsafe {
        let value = zeroed_box.assume_init();
        println!("零初始化的值: {}", value); // 输出: 0
    }

    // 重新创建以演示写入
    let mut zeroed_box2: Box<MaybeUninit<i32>> = Box::new_zeroed();
    unsafe {
        zeroed_box2.write(42);
        let value = zeroed_box2.assume_init();
        println!("写入后的值: {}", value); // 输出: 42
    }
}

/// 演示 Box::new_zeroed_slice 的使用
fn demonstrate_box_new_zeroed_slice() {
    println!("\n=== Box::new_zeroed_slice 演示 ===");

    // Rust 1.92.0: 创建零初始化的切片
    // 返回 Box<[MaybeUninit<u8>]>，所有元素被零初始化
    let mut zeroed_slice: Box<[MaybeUninit<u8>]> = Box::new_zeroed_slice(10);

    unsafe {
        // 读取零初始化的值 - 使用 assume_init_read() 或直接访问
        println!("零初始化的切片长度: {}", zeroed_slice.len());

        // 检查前5个元素是否为零（通过读取）
        let mut first_five = [0u8; 5];
        for i in 0..5 {
            first_five[i] = zeroed_slice[i].assume_init_read();
        }
        println!("前5个元素: {:?}", first_five); // 输出: [0, 0, 0, 0, 0]

        // 写入一些值
        for i in 0..5 {
            zeroed_slice[i].write(i as u8);
        }

        // 读取写入后的值
        let mut after_write = [0u8; 5];
        for i in 0..5 {
            after_write[i] = zeroed_slice[i].assume_init_read();
        }
        println!("写入后的前5个元素: {:?}", after_write); // 输出: [0, 1, 2, 3, 4]
    }
}

/// 演示 Rc::new_zeroed 的使用
fn demonstrate_rc_new_zeroed() {
    println!("\n=== Rc::new_zeroed 演示 ===");

    use std::rc::Rc;

    // Rust 1.92.0: 创建零初始化的 Rc
    let mut zeroed_rc: Rc<MaybeUninit<i32>> = Rc::new_zeroed();

    unsafe {
        // 注意：Rc 是不可变的，所以我们需要使用 Rc::get_mut 或 Rc::make_mut
        if let Some(mut_ref) = Rc::get_mut(&mut zeroed_rc) {
            mut_ref.write(100);
        }

        let value = zeroed_rc.assume_init();
        println!("Rc 零初始化的值: {}", value);
    }
}

/// 演示 Arc::new_zeroed 的使用（线程安全版本）
fn demonstrate_arc_new_zeroed() {
    println!("\n=== Arc::new_zeroed 演示 ===");

    use std::sync::Arc;

    // Rust 1.92.0: 创建零初始化的 Arc（线程安全）
    let mut zeroed_arc: Arc<MaybeUninit<i32>> = Arc::new_zeroed();

    unsafe {
        // Arc 也是不可变的，需要使用 Arc::get_mut 或 Arc::make_mut
        if let Some(mut_ref) = Arc::get_mut(&mut zeroed_arc) {
            mut_ref.write(200);
        }

        let value = zeroed_arc.assume_init();
        println!("Arc 零初始化的值: {}", value);
    }
}

/// 实际应用示例：零初始化的缓冲区
fn demonstrate_zeroed_buffer() {
    println!("\n=== 零初始化缓冲区应用示例 ===");

    // 创建一个零初始化的缓冲区，用于网络编程或文件 I/O
    let buffer: Box<[MaybeUninit<u8>]> = Box::new_zeroed_slice(1024);

    unsafe {
        println!("缓冲区大小: {} 字节", buffer.len());

        // 检查前10个字节是否为零
        let mut first_ten = [0u8; 10];
        for i in 0..10 {
            first_ten[i] = buffer[i].assume_init_read();
        }
        println!("前10个字节都是0: {:?}", first_ten);

        // 在实际应用中，可以安全地写入数据
        // 例如：从网络读取数据到缓冲区
    }
}

fn main() {
    println!("🚀 Rust 1.92.0 零初始化内存分配演示\n");

    demonstrate_box_new_zeroed();
    demonstrate_box_new_zeroed_slice();
    demonstrate_rc_new_zeroed();
    demonstrate_arc_new_zeroed();
    demonstrate_zeroed_buffer();

    println!("\n✅ 演示完成！");
    println!("\n💡 提示:");
    println!("  - Box::new_zeroed 类似于 C 的 calloc");
    println!("  - 返回 MaybeUninit<T>，需要使用 assume_init()");
    println!("  - 适用于需要零初始化内存的场景（如 FFI、网络编程）");
    println!("  - 性能优于先分配再清零的方式");
}
