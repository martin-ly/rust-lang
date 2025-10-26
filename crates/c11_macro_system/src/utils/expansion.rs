//! 宏展开辅助工具

/// 宏展开上下文信息
#[derive(Debug, Clone)]
pub struct ExpansionContext {
    /// 展开深度
    pub depth: usize,
    /// 是否启用调试
    pub debug: bool,
}

impl Default for ExpansionContext {
    fn default() -> Self {
        Self {
            depth: 0,
            debug: false,
        }
    }
}

impl ExpansionContext {
    /// 创建新的展开上下文
    pub fn new() -> Self {
        Self::default()
    }

    /// 增加展开深度
    pub fn increase_depth(&mut self) {
        self.depth += 1;
    }

    /// 启用调试模式
    pub fn enable_debug(&mut self) {
        self.debug = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expansion_context() {
        let mut ctx = ExpansionContext::new();
        assert_eq!(ctx.depth, 0);
        assert!(!ctx.debug);

        ctx.increase_depth();
        assert_eq!(ctx.depth, 1);

        ctx.enable_debug();
        assert!(ctx.debug);
    }
}

