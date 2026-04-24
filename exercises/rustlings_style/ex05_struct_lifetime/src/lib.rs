// 练习: 结构体生命周期
// 目标: 为 BorrowedString 添加生命周期参数
// 考点: 结构体包含引用时必须标注生命周期

pub struct BorrowedString {
    text: &str,
}

impl BorrowedString {
    pub fn new(text: &str) -> Self {
        Self { text }
    }

    pub fn text(&self) -> &str {
        self.text
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_borrowed_string() {
        let s = BorrowedString::new("hello");
        assert_eq!(s.text(), "hello");
    }
}
