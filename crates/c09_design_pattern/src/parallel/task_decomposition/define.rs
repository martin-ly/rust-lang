use rayon::prelude::*;

// 模拟任务处理的函数
#[allow(unused)]
fn process_task(task: i32) -> i32 {
    // 这里可以是任何复杂的计算
    task * task // 例如，返回任务的平方
}

#[allow(unused)]
pub fn task_decomposition_test() {
    // 假设我们有一个任务列表
    let tasks: Vec<i32> = (1..=10).collect();

    // 使用 rayon 的并行迭代器来处理任务
    let results: Vec<i32> = tasks
        .par_iter() // 转换为并行迭代器
        .map(|task| {
            // 这里是任务处理逻辑
            process_task(*task)
        })
        .collect();

    // 输出结果
    for result in results {
        println!("Result: {}", result);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_task_decomposition01() {
        task_decomposition_test();
    }
}
