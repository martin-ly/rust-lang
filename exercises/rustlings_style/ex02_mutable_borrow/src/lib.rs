// 练习: 修复可变借用冲突
// 目标: 让 append_and_print 能够编译
// 考点: 同一作用域内不能同时存在可变和不可变引用

pub fn append_and_print(s: &mut String) {
    let prefix = &s[..2]; // 不可变借用
    s.push_str(" world"); // 错误: 这里尝试可变借用，但 prefix 仍然有效
    println!("{} -> {}", prefix, s);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_append_and_print() {
        let mut s = String::from("hi");
        append_and_print(&mut s);
        assert_eq!(s, "hi world");
    }
}
