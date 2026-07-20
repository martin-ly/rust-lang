//使用闭包来设计算法和程序具有灵活性、简洁性、环境捕获、高阶函数支持和类型安全等多种优势。

#[allow(unused)]
pub fn filter_and_map<F, G, T, U>(data: Vec<T>, filter_fn: F, map_fn: G) -> Vec<U>
where
    F: Fn(&T) -> bool,
    G: Fn(T) -> U,
{
    data.into_iter()
        .filter(filter_fn) // 使用闭包进行过滤
        .map(map_fn) // 使用闭包进行映射
        .collect() // 收集结果
}

#[allow(unused)]
pub fn test_filter_and_map() {
    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // 定义过滤条件：只保留偶数
    let filter_fn = |x: &i32| *x % 2 == 0;

    // 定义映射逻辑：将每个数字乘以 2
    let map_fn = |x| x * 2;

    // 使用闭包进行过滤和映射
    let result = filter_and_map(numbers, filter_fn, map_fn);

    println!("{:?}", result); // 输出 [4, 8, 12, 16, 20]
}
