use std::thread;

struct Data {
    value: i32,
}

impl Data {
    fn new(value: i32) -> Self {
        Data { value }
    }

    fn process(self) -> i32 {
        // 模拟一些处理
        println!("Processing value: {}", self.value);
        self.value * 2 // 返回处理后的值
    }
}

fn main() {
    let data1 = Data::new(10);
    let data2 = Data::new(20);

    // 创建线程并移动数据到线程中
    let handle1 = thread::spawn(move || data1.process());

    let handle2 = thread::spawn(move || data2.process());

    // 等待线程完成并获取结果
    let result1 = handle1.join().unwrap();
    let result2 = handle2.join().unwrap();

    println!("Result from thread 1: {}", result1);
    println!("Result from thread 2: {}", result2);
}

// 该代码说明：
//函数 Data::new：创建一个新的 Data 实例。
//函数 Data::process：模拟一些处理并返回处理后的值。
//main 函数：创建两个 Data 实例，然后创建两个线程来处理这些数据。
//移动语义：
//在这个示例中，move 关键字用于将 data1 和 data2 的所有权转移到线程中。
//这样可以确保每个线程拥有独立的数据副本，避免了数据竞争和悬垂引用的问题。
//每个线程在处理数据时都可以安全地使用其拥有的 Data 实例。
