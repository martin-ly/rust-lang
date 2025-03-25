

#[allow(unused)]
fn is_valid(s: String) -> bool {
    let mut stack = Vec::new(); // 创建一个栈用于存储开括号
    
    for c in s.chars() {
        match c {
            '(' | '[' | '{' => stack.push(c), // 遇到开括号就入栈
            ')' => {
                // 遇到闭括号，检查栈顶是否匹配
                if stack.pop() != Some('(') {
                    return false;
                }
            },
            ']' => {
                if stack.pop() != Some('[') {
                    return false;
                }
            },
            '}' => {
                if stack.pop() != Some('{') {
                    return false;
                }
            },
            _ => return false, // 遇到其他字符，返回 false
        }
    }
    
    stack.is_empty() // 如果栈为空，说明所有括号都匹配
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_valid() {
        assert_eq!(is_valid("()".to_string()), true);
        assert_eq!(is_valid("([])".to_string()), true);
        assert_eq!(is_valid("([)]".to_string()), false);
        assert_eq!(is_valid("({})".to_string()), true);
        assert_eq!(is_valid("({)".to_string()), false);
        assert_eq!(is_valid(")".to_string()), false);
        assert_eq!(is_valid("()[]{}".to_string()), true); // 有效
        assert_eq!(is_valid("([)]".to_string()), false); // 无效
        assert_eq!(is_valid("{[()]}".to_string()), true); // 有效
        assert_eq!(is_valid("((()".to_string()), false); // 无效
    }
}


