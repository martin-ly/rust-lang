//! # Rust 作用域管理模块 / Rust Scope Management Module
//! 
//! 本模块提供了完整的 Rust 作用域管理功能，包括作用域栈、变量生命周期跟踪、
//! 作用域进入/退出管理等功能。
//! This module provides complete Rust scope management functionality, including scope stack,
//! variable lifecycle tracking, scope entry/exit management, etc.

use std::collections::HashMap;
use std::fmt;

/// 作用域类型枚举 / Scope Type Enum
#[derive(Debug, Clone, PartialEq)]
pub enum ScopeType {
    /// 代码块作用域 / Code Block Scope
    Block,
    /// 函数作用域 / Function Scope
    Function,
    /// 模块作用域 / Module Scope
    Module,
    /// 循环作用域 / Loop Scope
    Loop,
    /// 条件分支作用域 / Conditional Branch Scope
    Conditional,
    /// 表达式作用域 / Expression Scope
    Expression,
}

/// 作用域结构体 / Scope Struct
#[derive(Debug, Clone)]
pub struct Scope {
    /// 作用域名称 / Scope Name
    pub name: String,
    /// 作用域类型 / Scope Type
    pub scope_type: ScopeType,
    /// 作用域中的变量 / Variables in Scope
    pub variables: Vec<String>,
    /// 父作用域引用 / Parent Scope Reference
    pub parent: Option<String>,
    /// 作用域深度 / Scope Depth
    pub depth: usize,
    /// 创建时间戳 / Creation Timestamp
    pub created_at: std::time::Instant,
}

impl Scope {
    /// 创建新作用域 / Create New Scope
    pub fn new(name: String, scope_type: ScopeType, depth: usize) -> Self {
        Self {
            name,
            scope_type,
            variables: Vec::new(),
            parent: None,
            depth,
            created_at: std::time::Instant::now(),
        }
    }
    
    /// 添加变量到作用域 / Add Variable to Scope
    pub fn add_variable(&mut self, variable_name: String) {
        if !self.variables.contains(&variable_name) {
            self.variables.push(variable_name);
        }
    }
    
    /// 从作用域移除变量 / Remove Variable from Scope
    pub fn remove_variable(&mut self, variable_name: &str) -> bool {
        if let Some(pos) = self.variables.iter().position(|x| x == variable_name) {
            self.variables.remove(pos);
            true
        } else {
            false
        }
    }
    
    /// 检查变量是否在作用域中 / Check if Variable is in Scope
    pub fn contains_variable(&self, variable_name: &str) -> bool {
        self.variables.contains(&variable_name.to_string())
    }
    
    /// 获取作用域信息 / Get Scope Information
    pub fn get_info(&self) -> String {
        format!(
            "Scope: {} (Type: {:?}, Depth: {}, Variables: {})",
            self.name,
            self.scope_type,
            self.depth,
            self.variables.len()
        )
    }
}

/// 作用域错误类型 / Scope Error Types
#[derive(Debug, Clone)]
pub enum ScopeError {
    /// 没有作用域可退出 / No Scope to Exit
    NoScopeToExit,
    /// 作用域名称已存在 / Scope Name Already Exists
    ScopeNameExists,
    /// 作用域未找到 / Scope Not Found
    ScopeNotFound,
    /// 变量未找到 / Variable Not Found
    VariableNotFound,
    /// 作用域深度错误 / Invalid Scope Depth
    InvalidDepth,
}

impl fmt::Display for ScopeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ScopeError::NoScopeToExit => write!(f, "No scope to exit"),
            ScopeError::ScopeNameExists => write!(f, "Scope name already exists"),
            ScopeError::ScopeNotFound => write!(f, "Scope not found"),
            ScopeError::VariableNotFound => write!(f, "Variable not found"),
            ScopeError::InvalidDepth => write!(f, "Invalid scope depth"),
        }
    }
}

impl std::error::Error for ScopeError {}

/// 作用域管理器 / Scope Manager
pub struct ScopeManager {
    /// 作用域栈 / Scope Stack
    scope_stack: Vec<Scope>,
    /// 作用域映射 / Scope Mapping
    scope_map: HashMap<String, Scope>,
    /// 变量映射 / Variable Mapping
    variable_map: HashMap<String, VariableInfo>,
    /// 当前作用域深度 / Current Scope Depth
    current_depth: usize,
}

/// 变量信息结构体 / Variable Information Struct
#[derive(Debug, Clone)]
pub struct VariableInfo {
    /// 变量名称 / Variable Name
    pub name: String,
    /// 变量类型 / Variable Type
    pub var_type: String,
    /// 变量值 / Variable Value
    pub value: String,
    /// 声明作用域 / Declaration Scope
    pub scope_name: String,
    /// 是否可变 / Is Mutable
    pub is_mutable: bool,
    /// 生命周期 / Lifetime
    pub lifetime: Option<String>,
    /// 创建时间 / Creation Time
    pub created_at: std::time::Instant,
}

impl VariableInfo {
    /// 创建新的变量信息 / Create New Variable Information
    pub fn new(
        name: String,
        var_type: String,
        value: String,
        scope_name: String,
        is_mutable: bool,
        lifetime: Option<String>,
    ) -> Self {
        Self {
            name,
            var_type,
            value,
            scope_name,
            is_mutable,
            lifetime,
            created_at: std::time::Instant::now(),
        }
    }
}

impl ScopeManager {
    /// 创建新的作用域管理器 / Create New Scope Manager
    pub fn new() -> Self {
        Self {
            scope_stack: Vec::new(),
            scope_map: HashMap::new(),
            variable_map: HashMap::new(),
            current_depth: 0,
        }
    }
    
    /// 进入作用域 / Enter Scope
    pub fn enter_scope(&mut self, name: String, scope_type: ScopeType) -> Result<(), ScopeError> {
        // 检查作用域名称是否已存在
        if self.scope_map.contains_key(&name) {
            return Err(ScopeError::ScopeNameExists);
        }
        
        let scope = Scope::new(name.clone(), scope_type, self.current_depth);
        self.scope_stack.push(scope.clone());
        self.scope_map.insert(name, scope);
        self.current_depth += 1;
        
        Ok(())
    }
    
    /// 退出作用域 / Exit Scope
    pub fn exit_scope(&mut self) -> Result<(), ScopeError> {
        if let Some(scope) = self.scope_stack.pop() {
            // 清理作用域中的变量
            for variable_name in &scope.variables {
                self.variable_map.remove(variable_name);
            }
            
            // 从作用域映射中移除
            self.scope_map.remove(&scope.name);
            
            // 减少深度
            if self.current_depth > 0 {
                self.current_depth -= 1;
            }
            
            Ok(())
        } else {
            Err(ScopeError::NoScopeToExit)
        }
    }
    
    /// 声明变量 / Declare Variable
    pub fn declare_variable(
        &mut self,
        name: String,
        var_type: String,
        value: String,
        is_mutable: bool,
        lifetime: Option<String>,
    ) -> Result<(), ScopeError> {
        // 检查变量名是否已存在
        if self.variable_map.contains_key(&name) {
            return Err(ScopeError::VariableNotFound);
        }
        
        // 获取当前作用域名称
        let current_scope_name = if let Some(current_scope) = self.scope_stack.last() {
            current_scope.name.clone()
        } else {
            return Err(ScopeError::ScopeNotFound);
        };
        
        let variable_info = VariableInfo::new(
            name.clone(),
            var_type,
            value,
            current_scope_name.clone(),
            is_mutable,
            lifetime,
        );
        
        // 添加到变量映射
        self.variable_map.insert(name.clone(), variable_info);
        
        // 添加到当前作用域
        if let Some(current_scope) = self.scope_stack.last_mut() {
            current_scope.add_variable(name);
        }
        
        Ok(())
    }
    
    /// 查找变量 / Find Variable
    pub fn find_variable(&self, name: &str) -> Option<&VariableInfo> {
        self.variable_map.get(name)
    }
    
    /// 获取当前作用域 / Get Current Scope
    pub fn get_current_scope(&self) -> Option<&Scope> {
        self.scope_stack.last()
    }
    
    /// 获取作用域栈深度 / Get Scope Stack Depth
    pub fn get_scope_depth(&self) -> usize {
        self.scope_stack.len()
    }
    
    /// 获取所有作用域信息 / Get All Scope Information
    pub fn get_all_scopes(&self) -> Vec<String> {
        self.scope_stack
            .iter()
            .map(|scope| scope.get_info())
            .collect()
    }
    
    /// 获取所有变量信息 / Get All Variable Information
    pub fn get_all_variables(&self) -> Vec<&VariableInfo> {
        self.variable_map.values().collect()
    }
    
    /// 检查变量是否在当前作用域中可见 / Check if Variable is Visible in Current Scope
    pub fn is_variable_visible(&self, variable_name: &str) -> bool {
        // 从当前作用域开始向上查找
        for scope in self.scope_stack.iter().rev() {
            if scope.contains_variable(variable_name) {
                return true;
            }
        }
        false
    }
    
    /// 获取变量的作用域路径 / Get Variable Scope Path
    pub fn get_variable_scope_path(&self, variable_name: &str) -> Option<Vec<String>> {
        let mut path = Vec::new();
        
        for scope in &self.scope_stack {
            if scope.contains_variable(variable_name) {
                path.push(scope.name.clone());
                break;
            }
            path.push(scope.name.clone());
        }
        
        if path.is_empty() {
            None
        } else {
            Some(path)
        }
    }
}

/// 作用域分析器 / Scope Analyzer
pub struct ScopeAnalyzer {
    /// 作用域管理器引用 / Scope Manager Reference
    scope_manager: ScopeManager,
}

impl ScopeAnalyzer {
    /// 创建新的作用域分析器 / Create New Scope Analyzer
    pub fn new(scope_manager: ScopeManager) -> Self {
        Self { scope_manager }
    }
    
    /// 分析作用域嵌套关系 / Analyze Scope Nesting Relationships
    pub fn analyze_nesting(&self) -> Vec<String> {
        let mut analysis = Vec::new();
        
        for (i, scope) in self.scope_manager.scope_stack.iter().enumerate() {
            let indent = "  ".repeat(i);
            analysis.push(format!(
                "{}├─ {} (Depth: {}, Type: {:?})",
                indent, scope.name, scope.depth, scope.scope_type
            ));
        }
        
        analysis
    }
    
    /// 分析变量生命周期 / Analyze Variable Lifecycle
    pub fn analyze_variable_lifecycle(&self) -> Vec<String> {
        let mut analysis = Vec::new();
        
        for variable in self.scope_manager.get_all_variables() {
            if let Some(path) = self.scope_manager.get_variable_scope_path(&variable.name) {
                analysis.push(format!(
                    "Variable: {} (Type: {}, Scope: {:?}, Mutable: {})",
                    variable.name, variable.var_type, path, variable.is_mutable
                ));
            }
        }
        
        analysis
    }
    
    /// 检测潜在的内存泄漏 / Detect Potential Memory Leaks
    pub fn detect_memory_leaks(&self) -> Vec<String> {
        let mut leaks = Vec::new();
        
        // 检查是否有变量在作用域外仍然被引用
        for variable in self.scope_manager.get_all_variables() {
            if !self.scope_manager.is_variable_visible(&variable.name) {
                leaks.push(format!(
                    "Potential memory leak: Variable '{}' is not visible in current scope",
                    variable.name
                ));
            }
        }
        
        leaks
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_scope_creation() {
        let mut manager = ScopeManager::new();
        assert_eq!(manager.get_scope_depth(), 0);
        
        manager.enter_scope("test".to_string(), ScopeType::Block).unwrap();
        assert_eq!(manager.get_scope_depth(), 1);
    }
    
    #[test]
    fn test_variable_declaration() {
        let mut manager = ScopeManager::new();
        manager.enter_scope("test".to_string(), ScopeType::Block).unwrap();
        
        manager.declare_variable(
            "x".to_string(),
            "i32".to_string(),
            "42".to_string(),
            false,
            None,
        ).unwrap();
        
        assert!(manager.find_variable("x").is_some());
    }
    
    #[test]
    fn test_scope_exit() {
        let mut manager = ScopeManager::new();
        manager.enter_scope("test".to_string(), ScopeType::Block).unwrap();
        manager.enter_scope("inner".to_string(), ScopeType::Block).unwrap();
        
        assert_eq!(manager.get_scope_depth(), 2);
        
        manager.exit_scope().unwrap();
        assert_eq!(manager.get_scope_depth(), 1);
    }
}
