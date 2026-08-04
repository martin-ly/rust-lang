use crossbeam::channel;
use std::thread;
// 使用示例
#[allow(unused)]
pub fn parallel_pipeline_test() {
    // 创建通道
    let (tx1, rx1) = channel::bounded(10);
    let (tx2, rx2) = channel::bounded(10);

    // 克隆发送者和接收者 不使用clone就没必要drop , move语义 会转移所有权
    let tx1_clone = tx1.clone();
    let tx2_clone = tx2.clone();

    // 第一个阶段
    let producer = thread::spawn(move || {
        for i in 0..10 {
            tx1_clone.send(i).unwrap();
        }
    });

    // 第二个阶段
    let stage1 = thread::spawn(move || {
        for value in rx1.iter() {
            let processed_value = value * 2; // 处理数据
            tx2_clone.send(processed_value).unwrap();
        }
    });

    // 第三个阶段
    let consumer = thread::spawn(move || {
        for value in rx2.iter() {
            println!("Received: {}", value);
        }
    });

    // 等待所有线程完成
    producer.join().unwrap();
    drop(tx1); // 关闭第一个通道
    stage1.join().unwrap();
    drop(tx2); // 关闭第二个通道
    consumer.join().unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_pipeline01() {
        parallel_pipeline_test();
    }
}
