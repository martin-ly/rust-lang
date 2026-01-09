//! 宏调试工具

/// 宏调试信息
#[derive(Debug)]
pub struct MacroDebugInfo {
    /// 宏名称
    pub name: String,
    /// 调用位置
    pub location: String,
    /// 展开次数
    pub expansions: usize,
}

impl MacroDebugInfo {
    /// 创建新的调试信息
    pub fn new(name: impl Into<String>, location: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            location: location.into(),
            expansions: 0,
        }
    }

    /// 记录一次展开
    pub fn record_expansion(&mut self) {
        self.expansions += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_macro_debug_info() {
        let mut info = MacroDebugInfo::new("test_macro", "test.rs:10");
        assert_eq!(info.name, "test_macro");
        assert_eq!(info.expansions, 0);

        info.record_expansion();
        assert_eq!(info.expansions, 1);
    }
}
