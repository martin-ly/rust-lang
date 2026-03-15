//! C03 控制流练习 - 模式匹配
//! 
//! 运行: cargo test --package c03_control_flow -- exercises::pattern_matching

#[cfg(test)]
mod tests {
    /// 练习 1: 解构结构体
    struct Point {
        x: i32,
        y: i32,
    }

    fn get_quadrant(point: &Point) -> &'static str {
        match (point.x, point.y) {
            (0, 0) => "origin",
            (x, y) if x > 0 && y > 0 => "quadrant I",
            (x, y) if x < 0 && y > 0 => "quadrant II",
            (x, y) if x < 0 && y < 0 => "quadrant III",
            (x, y) if x > 0 && y < 0 => "quadrant IV",
            _ => "on axis",
        }
    }

    #[test]
    fn test_quadrant() {
        assert_eq!(get_quadrant(&Point { x: 0, y: 0 }), "origin");
        assert_eq!(get_quadrant(&Point { x: 3, y: 4 }), "quadrant I");
        assert_eq!(get_quadrant(&Point { x: -3, y: 4 }), "quadrant II");
        assert_eq!(get_quadrant(&Point { x: 0, y: 5 }), "on axis");
    }

    /// 练习 2: if let 简化模式
    enum Message {
        Text(String),
        Number(i32),
        Empty,
    }

    fn get_text_content(msg: &Message) -> Option<&str> {
        if let Message::Text(ref text) = msg {
            Some(text)
        } else {
            None
        }
    }

    #[test]
    fn test_if_let() {
        let msg = Message::Text(String::from("hello"));
        assert_eq!(get_text_content(&msg), Some("hello"));
        
        let num = Message::Number(42);
        assert_eq!(get_text_content(&num), None);
    }

    /// 练习 3: while let 循环
    fn process_items<T>(items: &mut Vec<T>) -> Vec<T> {
        let mut processed = Vec::new();
        while let Some(item) = items.pop() {
            processed.push(item);
        }
        processed
    }

    #[test]
    fn test_while_let() {
        let mut items = vec![1, 2, 3, 4, 5];
        let processed = process_items(&mut items);
        assert_eq!(processed, vec![5, 4, 3, 2, 1]);
        assert!(items.is_empty());
    }

    /// 练习 4: 守卫子句
    fn describe_number(n: i32) -> &'static str {
        match n {
            n if n < 0 => "negative",
            0 => "zero",
            n if n % 2 == 0 => "positive even",
            _ => "positive odd",
        }
    }

    #[test]
    fn test_guard_clauses() {
        assert_eq!(describe_number(-5), "negative");
        assert_eq!(describe_number(0), "zero");
        assert_eq!(describe_number(4), "positive even");
        assert_eq!(describe_number(3), "positive odd");
    }

    /// 练习 5: @ 绑定
    fn analyze_range(range: (i32, i32)) -> String {
        match range {
            (start, end) @ (0..=10, 0..=10) => {
                format!("Small range: {} to {}", start, end)
            }
            (start, end) if start == end => {
                format!("Empty range at {}", start)
            }
            (start, end) => {
                format!("Range: {} to {}", start, end)
            }
        }
    }

    #[test]
    fn test_at_binding() {
        assert_eq!(analyze_range((5, 8)), "Small range: 5 to 8");
        assert_eq!(analyze_range((10, 10)), "Empty range at 10");
        assert_eq!(analyze_range((0, 100)), "Range: 0 to 100");
    }
}
