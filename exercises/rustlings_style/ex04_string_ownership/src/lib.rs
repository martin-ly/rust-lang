// 练习: String 所有权转移
// 目标: 修复函数，使其接受 &str 而不是 String
// 考点: String 会转移所有权，&str 不会

pub fn count_words(text: String) -> usize {
    text.split_whitespace().count()
}

pub fn process_text() -> usize {
    let s = String::from("hello world rust");
    let c1 = count_words(s);
    let c2 = count_words(s); // 错误: s 的所有权已在上一行转移
    c1 + c2
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_process_text() {
        assert_eq!(process_text(), 6);
    }
}
