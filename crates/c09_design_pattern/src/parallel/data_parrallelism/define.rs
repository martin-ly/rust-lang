use rayon::prelude::*;

// 定义一个泛型函数，处理数据并行
pub fn parallel_process<T, F>(data: &mut [T], process_fn: F)
where
    T: Send + Sync,   // 确保 T 可以在多个线程中安全使用
    F: Fn(&T) + Sync, // 处理函数需要是线程安全的
{
    data.par_iter().for_each(|item| {
        process_fn(item);
    });
}

// 使用示例
#[allow(unused)]
pub fn parallel_process_test() {
    let mut data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // 定义一个处理函数
    let process_fn = |&x: &i32| {
        println!("Processing item: {}", x);
    };

    // 调用并行处理函数
    parallel_process(&mut data, process_fn);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_process01() {
        parallel_process_test();
    }
}
