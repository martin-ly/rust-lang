// 练习: 迭代器消费规则
// 目标: 修复两次消费迭代器的错误
// 考点: 迭代器只能消费一次

pub fn sum_and_count(values: Vec<i32>) -> (i32, usize) {
    let iter = values.into_iter();
    let sum: i32 = iter.sum();
    let count = iter.count(); // 错误: iter 已经被 sum() 消费了
    (sum, count)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sum_and_count() {
        assert_eq!(sum_and_count(vec![1, 2, 3]), (6, 3));
    }
}
