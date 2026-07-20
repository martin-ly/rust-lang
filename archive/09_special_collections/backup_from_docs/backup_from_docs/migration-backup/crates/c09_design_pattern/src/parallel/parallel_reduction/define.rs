use rayon::prelude::*;

// 定义一个并行归约函数
#[allow(unused)]
fn parallel_reduction<T, F>(data: &[T], reducer: F) -> T
where
    T: Send + Sync + Copy + std::ops::Add<Output = T>,
    F: Fn(T, T) -> T + Sync + Send,
{
    data.par_iter()
        .cloned()
        .reduce_with(reducer)
        .unwrap_or_else(|| panic!("No elements to reduce"))
}

// 使用示例
#[allow(unused)]
pub fn parallel_reduction_test() {
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // 使用并行归约计算总和
    let sum = parallel_reduction(&data, |a, b| a + b);
    println!("Sum: {}", sum);

    // 使用并行归约计算乘积
    let product = parallel_reduction(&data, |a, b| a * b);
    println!("Product: {}", product);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_reduction01() {
        parallel_reduction_test();
    }
}
