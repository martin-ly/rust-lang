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

#[allow(unused)]
pub fn make_pipeline_iter<'a>(input: &'a [i32]) -> impl Iterator<Item = i32> + Send + 'a {
    // 阶段1：映射
    let stage1 = input.iter().map(|v| v * 2);
    // 阶段2：过滤
    let stage2 = stage1.filter(|v| *v % 3 == 0);
    // 阶段3：再次映射
    stage2.map(|v| v + 1)
}

/// 可插拔阶段：使用函数指针实现类型擦除，便于组合
#[allow(unused)]
pub enum StageFn {
    Map(fn(i32) -> i32),
    Filter(fn(&i32) -> bool),
}

/// 根据阶段列表构建流水线，返回位 impl Iterator + Send
#[allow(unused)]
pub fn make_pluggable_iter<'a>(input: &'a [i32], stages: &'a [StageFn]) -> Box<dyn Iterator<Item = i32> + Send + 'a> {
    let mut it: Box<dyn Iterator<Item = i32> + Send + 'a> = Box::new(input.iter().copied());
    for stage in stages {
        it = match stage {
            StageFn::Map(f) => Box::new(it.map(move |v| f(v))),
            StageFn::Filter(p) => Box::new(it.filter(move |v| p(&v))),
        };
    }
    it
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_pipeline01() {
        parallel_pipeline_test();
    }
}

#[cfg(test)]
mod pluggable_tests {
    use super::*;

    fn double(x: i32) -> i32 { x * 2 }
    fn is_div3(x: &i32) -> bool { *x % 3 == 0 }

    #[test]
    fn test_make_pluggable_iter() {
        let data = [1, 2, 3, 4, 5, 6];
        let stages = [StageFn::Map(double), StageFn::Filter(is_div3), StageFn::Map(|v| v + 1)];
        let out: Vec<i32> = make_pluggable_iter(&data, &stages).collect();
        assert_eq!(out, vec![7, 13]);
    }
}

#[cfg(test)]
mod iter_tests {
    use super::*;

    #[test]
    fn test_make_pipeline_iter() {
        let data = [1, 2, 3, 4, 5, 6];
        let out: Vec<i32> = make_pipeline_iter(&data).collect();
        assert_eq!(out, vec![7, 13]);
    }
}
