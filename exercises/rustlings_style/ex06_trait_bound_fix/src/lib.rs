// 练习: 特质约束缺失
// 目标: 为泛型函数添加必要的 trait bound
// 考点: 使用 > 比较需要 PartialOrd，打印需要 Display

pub fn print_max<T>(a: T, b: T) {
    if a > b {
        println!("max = {}", a);
    } else {
        println!("max = {}", b);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_print_max() {
        print_max(10, 20);
        print_max(3.14, 2.71);
    }
}
