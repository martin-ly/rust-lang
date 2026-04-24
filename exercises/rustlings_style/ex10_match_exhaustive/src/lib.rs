// 练习: match 穷尽性检查
// 目标: 补全 match 分支
// 考点: match 必须覆盖所有可能的变体

#[derive(Debug, PartialEq)]
pub enum Direction {
    North,
    South,
    East,
    West,
}

pub fn describe(direction: Direction) -> &'static str {
    match direction {
        Direction::North => "向北",
        Direction::South => "向南",
        // 错误: 缺少 East 和 West 的处理
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_describe() {
        assert_eq!(describe(Direction::North), "向北");
        assert_eq!(describe(Direction::East), "向东");
    }
}
