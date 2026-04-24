// 练习: 修复借用错误
// 目标: 让这个函数能够编译，同时不改变函数签名
// 考点: &String 借用 vs String 所有权转移

pub fn print_and_return_length(s: String) -> usize {
    let len = get_length(&s);
    println!("长度是: {}", len);
    // 这里需要返回 s 的长度，但 s 已经被借用了
    // 提示: get_length 接收 &String，所以 s 应该仍然可用
    s.len()
}

fn get_length(s: &String) -> usize {
    s.len()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_print_and_return_length() {
        assert_eq!(print_and_return_length(String::from("hello")), 5);
    }
}
