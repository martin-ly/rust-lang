//! 高级模式匹配模块
//!
//! 本模块展示了 Rust 1.90 中的高级模式匹配特性，包括：
//! - 复杂枚举模式匹配
//! - 守卫条件
//! - 解构模式
//! - 嵌套模式
//! - 动态模式匹配
//! - 模式匹配优化
//!
//! # 文件信息
//! - 文件: advanced_pattern_matching.rs
//! - 创建日期: 2025-01-27
//! - 版本: 1.0
//! - Rust版本: 1.90.0
//! - Edition: 2024

use std::collections::{HashMap};
use std::fmt;

// ==================== 1. 复杂枚举模式匹配 ====================

/// 复杂表达式枚举
/// 
/// 展示了复杂的枚举模式匹配
#[derive(Debug, Clone, PartialEq)]
pub enum ComplexExpression {
    /// 字面量
    Literal(LiteralValue),
    /// 变量
    Variable(String),
    /// 二元运算
    BinaryOp {
        left: Box<ComplexExpression>,
        operator: BinaryOperator,
        right: Box<ComplexExpression>,
    },
    /// 一元运算
    UnaryOp {
        operator: UnaryOperator,
        operand: Box<ComplexExpression>,
    },
    /// 函数调用
    FunctionCall {
        name: String,
        arguments: Vec<ComplexExpression>,
    },
    /// 条件表达式
    Conditional {
        condition: Box<ComplexExpression>,
        true_branch: Box<ComplexExpression>,
        false_branch: Box<ComplexExpression>,
    },
    /// 数组访问
    ArrayAccess {
        array: Box<ComplexExpression>,
        index: Box<ComplexExpression>,
    },
    /// 对象访问
    ObjectAccess {
        object: Box<ComplexExpression>,
        field: String,
    },
}

/// 字面量值
#[derive(Debug, Clone, PartialEq)]
pub enum LiteralValue {
    Integer(i64),
    Float(f64),
    Boolean(bool),
    String(String),
    Null,
}

/// 二元运算符
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinaryOperator {
    Add, Sub, Mul, Div, Mod,
    Eq, Ne, Lt, Le, Gt, Ge,
    And, Or, Xor,
    Shl, Shr,
}

/// 一元运算符
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnaryOperator {
    Not, Neg, Pos, Inc, Dec,
}

impl fmt::Display for ComplexExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ComplexExpression::Literal(lit) => write!(f, "{}", lit),
            ComplexExpression::Variable(name) => write!(f, "{}", name),
            ComplexExpression::BinaryOp { left, operator, right } => {
                write!(f, "({} {} {})", left, operator, right)
            },
            ComplexExpression::UnaryOp { operator, operand } => {
                write!(f, "{}{}", operator, operand)
            },
            ComplexExpression::FunctionCall { name, arguments } => {
                let args: Vec<String> = arguments.iter().map(|arg| format!("{}", arg)).collect();
                write!(f, "{}({})", name, args.join(", "))
            },
            ComplexExpression::Conditional { condition, true_branch, false_branch } => {
                write!(f, "({} ? {} : {})", condition, true_branch, false_branch)
            },
            ComplexExpression::ArrayAccess { array, index } => {
                write!(f, "{}[{}]", array, index)
            },
            ComplexExpression::ObjectAccess { object, field } => {
                write!(f, "{}.{}", object, field)
            },
        }
    }
}

impl fmt::Display for LiteralValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LiteralValue::Integer(i) => write!(f, "{}", i),
            LiteralValue::Float(fl) => write!(f, "{}", fl),
            LiteralValue::Boolean(b) => write!(f, "{}", b),
            LiteralValue::String(s) => write!(f, "\"{}\"", s),
            LiteralValue::Null => write!(f, "null"),
        }
    }
}

impl fmt::Display for BinaryOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinaryOperator::Add => write!(f, "+"),
            BinaryOperator::Sub => write!(f, "-"),
            BinaryOperator::Mul => write!(f, "*"),
            BinaryOperator::Div => write!(f, "/"),
            BinaryOperator::Mod => write!(f, "%"),
            BinaryOperator::Eq => write!(f, "=="),
            BinaryOperator::Ne => write!(f, "!="),
            BinaryOperator::Lt => write!(f, "<"),
            BinaryOperator::Le => write!(f, "<="),
            BinaryOperator::Gt => write!(f, ">"),
            BinaryOperator::Ge => write!(f, ">="),
            BinaryOperator::And => write!(f, "&&"),
            BinaryOperator::Or => write!(f, "||"),
            BinaryOperator::Xor => write!(f, "^"),
            BinaryOperator::Shl => write!(f, "<<"),
            BinaryOperator::Shr => write!(f, ">>"),
        }
    }
}

impl fmt::Display for UnaryOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnaryOperator::Not => write!(f, "!"),
            UnaryOperator::Neg => write!(f, "-"),
            UnaryOperator::Pos => write!(f, "+"),
            UnaryOperator::Inc => write!(f, "++"),
            UnaryOperator::Dec => write!(f, "--"),
        }
    }
}

/// 表达式求值器
pub struct ExpressionEvaluator {
    variables: HashMap<String, LiteralValue>,
}

impl ExpressionEvaluator {
    pub fn new() -> Self {
        Self {
            variables: HashMap::new(),
        }
    }
    
    pub fn set_variable(&mut self, name: String, value: LiteralValue) {
        self.variables.insert(name, value);
    }
    
    /// 高级模式匹配求值
    pub fn evaluate(&self, expr: &ComplexExpression) -> Result<LiteralValue, String> {
        match expr {
            // 字面量直接返回
            ComplexExpression::Literal(lit) => Ok(lit.clone()),
            
            // 变量查找
            ComplexExpression::Variable(name) => {
                self.variables.get(name)
                    .cloned()
                    .ok_or_else(|| format!("Undefined variable: {}", name))
            },
            
            // 二元运算 - 使用守卫条件
            ComplexExpression::BinaryOp { left, operator, right } => {
                let left_val = self.evaluate(left)?;
                let right_val = self.evaluate(right)?;
                
                match (left_val, operator, right_val) {
                    // 算术运算
                    (LiteralValue::Integer(a), BinaryOperator::Add, LiteralValue::Integer(b)) => {
                        Ok(LiteralValue::Integer(a + b))
                    },
                    (LiteralValue::Integer(a), BinaryOperator::Sub, LiteralValue::Integer(b)) => {
                        Ok(LiteralValue::Integer(a - b))
                    },
                    (LiteralValue::Integer(a), BinaryOperator::Mul, LiteralValue::Integer(b)) => {
                        Ok(LiteralValue::Integer(a * b))
                    },
                    (LiteralValue::Integer(a), BinaryOperator::Div, LiteralValue::Integer(b)) if b != 0 => {
                        Ok(LiteralValue::Integer(a / b))
                    },
                    (LiteralValue::Integer(_), BinaryOperator::Div, LiteralValue::Integer(0)) => {
                        Err("Division by zero".to_string())
                    },
                    
                    // 浮点运算
                    (LiteralValue::Float(a), BinaryOperator::Add, LiteralValue::Float(b)) => {
                        Ok(LiteralValue::Float(a + b))
                    },
                    (LiteralValue::Float(a), BinaryOperator::Sub, LiteralValue::Float(b)) => {
                        Ok(LiteralValue::Float(a - b))
                    },
                    (LiteralValue::Float(a), BinaryOperator::Mul, LiteralValue::Float(b)) => {
                        Ok(LiteralValue::Float(a * b))
                    },
                    (LiteralValue::Float(a), BinaryOperator::Div, LiteralValue::Float(b)) if b != 0.0 => {
                        Ok(LiteralValue::Float(a / b))
                    },
                    
                    // 比较运算
                    (a, BinaryOperator::Eq, b) => Ok(LiteralValue::Boolean(a == b)),
                    (a, BinaryOperator::Ne, b) => Ok(LiteralValue::Boolean(a != b)),
                    
                    // 布尔运算
                    (LiteralValue::Boolean(a), BinaryOperator::And, LiteralValue::Boolean(b)) => {
                        Ok(LiteralValue::Boolean(a && b))
                    },
                    (LiteralValue::Boolean(a), BinaryOperator::Or, LiteralValue::Boolean(b)) => {
                        Ok(LiteralValue::Boolean(a || b))
                    },
                    
                    // 类型不匹配
                    (a, op, b) => Err(format!("Invalid operation: {} {} {}", a, op, b)),
                }
            },
            
            // 一元运算
            ComplexExpression::UnaryOp { operator, operand } => {
                let val = self.evaluate(operand)?;
                match (operator, val) {
                    (UnaryOperator::Not, LiteralValue::Boolean(b)) => Ok(LiteralValue::Boolean(!b)),
                    (UnaryOperator::Neg, LiteralValue::Integer(i)) => Ok(LiteralValue::Integer(-i)),
                    (UnaryOperator::Neg, LiteralValue::Float(f)) => Ok(LiteralValue::Float(-f)),
                    (UnaryOperator::Pos, LiteralValue::Integer(i)) => Ok(LiteralValue::Integer(i)),
                    (UnaryOperator::Pos, LiteralValue::Float(f)) => Ok(LiteralValue::Float(f)),
                    (op, val) => Err(format!("Invalid unary operation: {} {}", op, val)),
                }
            },
            
            // 函数调用
            ComplexExpression::FunctionCall { name, arguments } => {
                let arg_values: Result<Vec<LiteralValue>, String> = 
                    arguments.iter().map(|arg| self.evaluate(arg)).collect();
                let arg_values = arg_values?;
                
                match name.as_str() {
                    "max" if arg_values.len() == 2 => {
                        match (&arg_values[0], &arg_values[1]) {
                            (LiteralValue::Integer(a), LiteralValue::Integer(b)) => {
                                Ok(LiteralValue::Integer(*a.max(b)))
                            },
                            (LiteralValue::Float(a), LiteralValue::Float(b)) => {
                                Ok(LiteralValue::Float(a.max(*b)))
                            },
                            _ => Err("max() requires two numbers".to_string()),
                        }
                    },
                    "min" if arg_values.len() == 2 => {
                        match (&arg_values[0], &arg_values[1]) {
                            (LiteralValue::Integer(a), LiteralValue::Integer(b)) => {
                                Ok(LiteralValue::Integer(*a.min(b)))
                            },
                            (LiteralValue::Float(a), LiteralValue::Float(b)) => {
                                Ok(LiteralValue::Float(a.min(*b)))
                            },
                            _ => Err("min() requires two numbers".to_string()),
                        }
                    },
                    "abs" if arg_values.len() == 1 => {
                        match &arg_values[0] {
                            LiteralValue::Integer(i) => Ok(LiteralValue::Integer(i.abs())),
                            LiteralValue::Float(f) => Ok(LiteralValue::Float(f.abs())),
                            _ => Err("abs() requires a number".to_string()),
                        }
                    },
                    _ => Err(format!("Unknown function: {}", name)),
                }
            },
            
            // 条件表达式
            ComplexExpression::Conditional { condition, true_branch, false_branch } => {
                let cond_val = self.evaluate(condition)?;
                match cond_val {
                    LiteralValue::Boolean(true) => self.evaluate(true_branch),
                    LiteralValue::Boolean(false) => self.evaluate(false_branch),
                    _ => Err("Condition must be boolean".to_string()),
                }
            },
            
            // 数组访问（简化实现）
            ComplexExpression::ArrayAccess { array, index } => {
                let _array_val = self.evaluate(array)?;
                let _index_val = self.evaluate(index)?;
                // 简化实现，实际中需要处理数组类型
                Err("Array access not implemented".to_string())
            },
            
            // 对象访问（简化实现）
            ComplexExpression::ObjectAccess { object, field } => {
                let _object_val = self.evaluate(object)?;
                // 简化实现，实际中需要处理对象类型
                Err(format!("Object field access '{}' not implemented", field))
            },
        }
    }
}

impl Default for ExpressionEvaluator {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 2. 动态模式匹配 ====================

/// 动态模式匹配器
/// 
/// 展示了运行时动态模式匹配
pub struct DynamicPatternMatcher {
    patterns: Vec<DynamicPattern>,
}

/// 动态模式
pub struct DynamicPattern {
    pub name: String,
    pub matcher: Box<dyn Fn(&ComplexExpression) -> bool + Send + Sync>,
    pub handler: Box<dyn Fn(&ComplexExpression) -> Result<LiteralValue, String> + Send + Sync>,
}

impl DynamicPatternMatcher {
    pub fn new() -> Self {
        Self {
            patterns: Vec::new(),
        }
    }
    
    /// 添加动态模式
    pub fn add_pattern<M, H>(&mut self, name: String, matcher: M, handler: H)
    where
        M: Fn(&ComplexExpression) -> bool + Send + Sync + 'static,
        H: Fn(&ComplexExpression) -> Result<LiteralValue, String> + Send + Sync + 'static,
    {
        self.patterns.push(DynamicPattern {
            name,
            matcher: Box::new(matcher),
            handler: Box::new(handler),
        });
    }
    
    /// 匹配并处理表达式
    pub fn match_and_handle(&self, expr: &ComplexExpression) -> Result<LiteralValue, String> {
        for pattern in &self.patterns {
            if (pattern.matcher)(expr) {
                return (pattern.handler)(expr);
            }
        }
        Err("No pattern matched".to_string())
    }
    
    /// 获取所有模式名称
    pub fn get_pattern_names(&self) -> Vec<String> {
        self.patterns.iter().map(|p| p.name.clone()).collect()
    }
}

impl Default for DynamicPatternMatcher {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 3. 模式匹配优化 ====================

/// 模式匹配优化器
/// 
/// 展示了模式匹配的性能优化技术
pub struct PatternMatchingOptimizer {
    cache: HashMap<String, LiteralValue>,
    optimization_stats: OptimizationStats,
}

/// 优化统计
#[derive(Debug, Default)]
pub struct OptimizationStats {
    pub cache_hits: u64,
    pub cache_misses: u64,
    pub pattern_matches: u64,
    pub optimizations_applied: u64,
}

impl PatternMatchingOptimizer {
    pub fn new() -> Self {
        Self {
            cache: HashMap::new(),
            optimization_stats: OptimizationStats::default(),
        }
    }
    
    /// 优化的表达式求值
    pub fn evaluate_optimized(&mut self, expr: &ComplexExpression) -> Result<LiteralValue, String> {
        // 生成缓存键
        let cache_key = self.generate_cache_key(expr);
        
        // 检查缓存
        if let Some(cached_result) = self.cache.get(&cache_key) {
            self.optimization_stats.cache_hits += 1;
            return Ok(cached_result.clone());
        }
        
        self.optimization_stats.cache_misses += 1;
        
        // 应用优化
        let optimized_expr = self.optimize_expression(expr);
        self.optimization_stats.optimizations_applied += 1;
        
        // 求值
        let evaluator = ExpressionEvaluator::new();
        let result = evaluator.evaluate(&optimized_expr)?;
        
        // 缓存结果
        self.cache.insert(cache_key, result.clone());
        
        Ok(result)
    }
    
    /// 生成缓存键
    fn generate_cache_key(&self, expr: &ComplexExpression) -> String {
        format!("{:?}", expr)
    }
    
    /// 优化表达式
    fn optimize_expression(&self, expr: &ComplexExpression) -> ComplexExpression {
        match expr {
            // 常量折叠优化
            ComplexExpression::BinaryOp { left, operator, right } => {
                match (left.as_ref(), right.as_ref()) {
                    (ComplexExpression::Literal(a), ComplexExpression::Literal(b)) => {
                        // 尝试常量折叠
                        if let Ok(result) = self.fold_constants(a, operator, b) {
                            return ComplexExpression::Literal(result);
                        }
                    },
                    _ => {},
                }
                
                // 递归优化子表达式
                ComplexExpression::BinaryOp {
                    left: Box::new(self.optimize_expression(left)),
                    operator: *operator,
                    right: Box::new(self.optimize_expression(right)),
                }
            },
            
            // 一元运算优化
            ComplexExpression::UnaryOp { operator, operand } => {
                match operand.as_ref() {
                    ComplexExpression::Literal(lit) => {
                        if let Ok(result) = self.fold_unary_constant(operator, lit) {
                            return ComplexExpression::Literal(result);
                        }
                    },
                    _ => {},
                }
                
                ComplexExpression::UnaryOp {
                    operator: *operator,
                    operand: Box::new(self.optimize_expression(operand)),
                }
            },
            
            // 其他表达式递归优化
            ComplexExpression::FunctionCall { name, arguments } => {
                let optimized_args: Vec<ComplexExpression> = 
                    arguments.iter().map(|arg| self.optimize_expression(arg)).collect();
                
                ComplexExpression::FunctionCall {
                    name: name.clone(),
                    arguments: optimized_args,
                }
            },
            
            ComplexExpression::Conditional { condition, true_branch, false_branch } => {
                ComplexExpression::Conditional {
                    condition: Box::new(self.optimize_expression(condition)),
                    true_branch: Box::new(self.optimize_expression(true_branch)),
                    false_branch: Box::new(self.optimize_expression(false_branch)),
                }
            },
            
            // 其他情况直接返回
            _ => expr.clone(),
        }
    }
    
    /// 常量折叠
    fn fold_constants(&self, a: &LiteralValue, op: &BinaryOperator, b: &LiteralValue) -> Result<LiteralValue, String> {
        match (a, op, b) {
            (LiteralValue::Integer(x), BinaryOperator::Add, LiteralValue::Integer(y)) => {
                Ok(LiteralValue::Integer(x + y))
            },
            (LiteralValue::Integer(x), BinaryOperator::Sub, LiteralValue::Integer(y)) => {
                Ok(LiteralValue::Integer(x - y))
            },
            (LiteralValue::Integer(x), BinaryOperator::Mul, LiteralValue::Integer(y)) => {
                Ok(LiteralValue::Integer(x * y))
            },
            (LiteralValue::Integer(x), BinaryOperator::Div, LiteralValue::Integer(y)) if *y != 0 => {
                Ok(LiteralValue::Integer(x / y))
            },
            (LiteralValue::Float(x), BinaryOperator::Add, LiteralValue::Float(y)) => {
                Ok(LiteralValue::Float(x + y))
            },
            (LiteralValue::Float(x), BinaryOperator::Sub, LiteralValue::Float(y)) => {
                Ok(LiteralValue::Float(x - y))
            },
            (LiteralValue::Float(x), BinaryOperator::Mul, LiteralValue::Float(y)) => {
                Ok(LiteralValue::Float(x * y))
            },
            (LiteralValue::Float(x), BinaryOperator::Div, LiteralValue::Float(y)) if *y != 0.0 => {
                Ok(LiteralValue::Float(x / y))
            },
            _ => Err("Cannot fold constants".to_string()),
        }
    }
    
    /// 一元常量折叠
    fn fold_unary_constant(&self, op: &UnaryOperator, lit: &LiteralValue) -> Result<LiteralValue, String> {
        match (op, lit) {
            (UnaryOperator::Neg, LiteralValue::Integer(i)) => Ok(LiteralValue::Integer(-i)),
            (UnaryOperator::Neg, LiteralValue::Float(f)) => Ok(LiteralValue::Float(-f)),
            (UnaryOperator::Not, LiteralValue::Boolean(b)) => Ok(LiteralValue::Boolean(!b)),
            _ => Err("Cannot fold unary constant".to_string()),
        }
    }
    
    /// 获取优化统计
    pub fn get_stats(&self) -> &OptimizationStats {
        &self.optimization_stats
    }
    
    /// 清空缓存
    pub fn clear_cache(&mut self) {
        self.cache.clear();
    }
}

impl Default for PatternMatchingOptimizer {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 4. 嵌套模式匹配 ====================

/// 嵌套数据结构
#[derive(Debug, Clone, PartialEq)]
pub enum NestedData {
    /// 叶子节点
    Leaf(String),
    /// 分支节点
    Branch {
        name: String,
        children: Vec<NestedData>,
    },
    /// 数组节点
    Array(Vec<NestedData>),
    /// 对象节点
    Object(HashMap<String, NestedData>),
}

/// 嵌套模式匹配器
pub struct NestedPatternMatcher;

impl NestedPatternMatcher {
    /// 深度优先搜索
    pub fn find_by_name<'a>(&self, data: &'a NestedData, target_name: &str) -> Vec<&'a NestedData> {
        let mut results = Vec::new();
        self.find_by_name_recursive(data, target_name, &mut results);
        results
    }
    
    fn find_by_name_recursive<'a>(&self, data: &'a NestedData, target_name: &str, results: &mut Vec<&'a NestedData>) {
        match data {
            NestedData::Leaf(name) if name == target_name => {
                results.push(data);
            },
            NestedData::Branch { name, children } => {
                if name == target_name {
                    results.push(data);
                }
                for child in children {
                    self.find_by_name_recursive(child, target_name, results);
                }
            },
            NestedData::Array(items) => {
                for item in items {
                    self.find_by_name_recursive(item, target_name, results);
                }
            },
            NestedData::Object(fields) => {
                for (key, value) in fields {
                    if key == target_name {
                        results.push(data);
                    }
                    self.find_by_name_recursive(value, target_name, results);
                }
            },
            _ => {},
        }
    }
    
    /// 模式匹配转换
    #[allow(dead_code)]
    #[allow(unused_variables)]
    pub fn transform<F>(&self, data: &NestedData, transformer: F) -> NestedData
    where
        F: Fn(&NestedData) -> NestedData + Clone,
    {
        match data {
            NestedData::Leaf(name) => transformer(data),
            NestedData::Branch { name, children } => {
                let transformed_children: Vec<NestedData> = children
                    .iter()
                    .map(|child| self.transform(child, transformer.clone()))
                    .collect();
                
                NestedData::Branch {
                    name: name.clone(),
                    children: transformed_children,
                }
            },
            NestedData::Array(items) => {
                let transformed_items: Vec<NestedData> = items
                    .iter()
                    .map(|item| self.transform(item, transformer.clone()))
                    .collect();
                
                NestedData::Array(transformed_items)
            },
            NestedData::Object(fields) => {
                let transformed_fields: HashMap<String, NestedData> = fields
                    .iter()
                    .map(|(key, value)| (key.clone(), self.transform(value, transformer.clone())))
                    .collect();
                
                NestedData::Object(transformed_fields)
            },
        }
    }
    
    /// 条件过滤
    pub fn filter<F>(&self, data: &NestedData, predicate: F) -> Option<NestedData>
    where
        F: Fn(&NestedData) -> bool + Clone,
    {
        if !predicate(data) {
            return None;
        }
        
        match data {
            NestedData::Leaf(_) => Some(data.clone()),
            NestedData::Branch { name, children } => {
                let filtered_children: Vec<NestedData> = children
                    .iter()
                    .filter_map(|child| self.filter(child, predicate.clone()))
                    .collect();
                
                Some(NestedData::Branch {
                    name: name.clone(),
                    children: filtered_children,
                })
            },
            NestedData::Array(items) => {
                let filtered_items: Vec<NestedData> = items
                    .iter()
                    .filter_map(|item| self.filter(item, predicate.clone()))
                    .collect();
                
                Some(NestedData::Array(filtered_items))
            },
            NestedData::Object(fields) => {
                let filtered_fields: HashMap<String, NestedData> = fields
                    .iter()
                    .filter_map(|(key, value)| {
                        self.filter(value, predicate.clone()).map(|v| (key.clone(), v))
                    })
                    .collect();
                
                Some(NestedData::Object(filtered_fields))
            },
        }
    }
}

// ==================== 演示函数 ====================

/// 演示所有高级模式匹配特性
pub fn demonstrate_advanced_pattern_matching() {
    println!("=== 高级模式匹配演示 ===\n");
    
    // 1. 复杂表达式模式匹配演示
    println!("1. 复杂表达式模式匹配演示:");
    let mut evaluator = ExpressionEvaluator::new();
    evaluator.set_variable("x".to_string(), LiteralValue::Integer(10));
    evaluator.set_variable("y".to_string(), LiteralValue::Integer(5));
    
    // 创建复杂表达式
    let expr = ComplexExpression::BinaryOp {
        left: Box::new(ComplexExpression::BinaryOp {
            left: Box::new(ComplexExpression::Variable("x".to_string())),
            operator: BinaryOperator::Add,
            right: Box::new(ComplexExpression::Literal(LiteralValue::Integer(3))),
        }),
        operator: BinaryOperator::Mul,
        right: Box::new(ComplexExpression::Variable("y".to_string())),
    };
    
    println!("  表达式: {}", expr);
    match evaluator.evaluate(&expr) {
        Ok(result) => println!("  求值结果: {}", result),
        Err(e) => println!("  求值错误: {}", e),
    }
    
    // 条件表达式
    let conditional_expr = ComplexExpression::Conditional {
        condition: Box::new(ComplexExpression::BinaryOp {
            left: Box::new(ComplexExpression::Variable("x".to_string())),
            operator: BinaryOperator::Gt,
            right: Box::new(ComplexExpression::Literal(LiteralValue::Integer(5))),
        }),
        true_branch: Box::new(ComplexExpression::Literal(LiteralValue::String("x > 5".to_string()))),
        false_branch: Box::new(ComplexExpression::Literal(LiteralValue::String("x <= 5".to_string()))),
    };
    
    println!("  条件表达式: {}", conditional_expr);
    match evaluator.evaluate(&conditional_expr) {
        Ok(result) => println!("  条件结果: {}", result),
        Err(e) => println!("  条件错误: {}", e),
    }
    println!();
    
    // 2. 动态模式匹配演示
    println!("2. 动态模式匹配演示:");
    let mut dynamic_matcher = DynamicPatternMatcher::new();
    
    // 添加动态模式
    dynamic_matcher.add_pattern(
        "literal_pattern".to_string(),
        |expr| matches!(expr, ComplexExpression::Literal(_)),
        |expr| {
            if let ComplexExpression::Literal(lit) = expr {
                Ok(lit.clone())
            } else {
                Err("Not a literal".to_string())
            }
        },
    );
    
    dynamic_matcher.add_pattern(
        "variable_pattern".to_string(),
        |expr| matches!(expr, ComplexExpression::Variable(_)),
        |expr| {
            if let ComplexExpression::Variable(name) = expr {
                Ok(LiteralValue::String(format!("Variable: {}", name)))
            } else {
                Err("Not a variable".to_string())
            }
        },
    );
    
    let patterns = dynamic_matcher.get_pattern_names();
    println!("  注册的模式: {:?}", patterns);
    
    let test_exprs = vec![
        ComplexExpression::Literal(LiteralValue::Integer(42)),
        ComplexExpression::Variable("test".to_string()),
    ];
    
    for expr in test_exprs {
        match dynamic_matcher.match_and_handle(&expr) {
            Ok(result) => println!("  匹配结果: {}", result),
            Err(e) => println!("  匹配错误: {}", e),
        }
    }
    println!();
    
    // 3. 模式匹配优化演示
    println!("3. 模式匹配优化演示:");
    let mut optimizer = PatternMatchingOptimizer::new();
    
    // 创建可优化的表达式
    let optimizable_expr = ComplexExpression::BinaryOp {
        left: Box::new(ComplexExpression::Literal(LiteralValue::Integer(10))),
        operator: BinaryOperator::Add,
        right: Box::new(ComplexExpression::Literal(LiteralValue::Integer(20))),
    };
    
    println!("  原始表达式: {}", optimizable_expr);
    match optimizer.evaluate_optimized(&optimizable_expr) {
        Ok(result) => println!("  优化结果: {}", result),
        Err(e) => println!("  优化错误: {}", e),
    }
    
    // 再次求值以测试缓存
    match optimizer.evaluate_optimized(&optimizable_expr) {
        Ok(result) => println!("  缓存结果: {}", result),
        Err(e) => println!("  缓存错误: {}", e),
    }
    
    let stats = optimizer.get_stats();
    println!("  优化统计: {:?}", stats);
    println!();
    
    // 4. 嵌套模式匹配演示
    println!("4. 嵌套模式匹配演示:");
    let nested_matcher = NestedPatternMatcher;
    
    // 创建嵌套数据结构
    let nested_data = NestedData::Branch {
        name: "root".to_string(),
        children: vec![
            NestedData::Leaf("leaf1".to_string()),
            NestedData::Branch {
                name: "branch1".to_string(),
                children: vec![
                    NestedData::Leaf("leaf2".to_string()),
                    NestedData::Array(vec![
                        NestedData::Leaf("array_leaf1".to_string()),
                        NestedData::Leaf("array_leaf2".to_string()),
                    ]),
                ],
            },
            NestedData::Object({
                let mut map = HashMap::new();
                map.insert("key1".to_string(), NestedData::Leaf("value1".to_string()));
                map.insert("key2".to_string(), NestedData::Leaf("value2".to_string()));
                map
            }),
        ],
    };
    
    println!("  嵌套数据结构: {:?}", nested_data);
    
    // 查找特定名称的节点
    let found_nodes = nested_matcher.find_by_name(&nested_data, "leaf1");
    println!("  找到的 'leaf1' 节点数量: {}", found_nodes.len());
    
    // 转换数据
    let transformed = nested_matcher.transform(&nested_data, |data| {
        match data {
            NestedData::Leaf(name) => NestedData::Leaf(format!("transformed_{}", name)),
            other => other.clone(),
        }
    });
    println!("  转换后的数据: {:?}", transformed);
    
    // 过滤数据
    let filtered = nested_matcher.filter(&nested_data, |data| {
        match data {
            NestedData::Leaf(name) => name.starts_with("leaf"),
            _ => true,
        }
    });
    println!("  过滤后的数据: {:?}", filtered);
    
    println!("\n=== 高级模式匹配演示完成 ===");
}

// ==================== 测试模块 ====================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_expression_evaluation() {
        let mut evaluator = ExpressionEvaluator::new();
        evaluator.set_variable("x".to_string(), LiteralValue::Integer(10));
        
        let expr = ComplexExpression::BinaryOp {
            left: Box::new(ComplexExpression::Variable("x".to_string())),
            operator: BinaryOperator::Add,
            right: Box::new(ComplexExpression::Literal(LiteralValue::Integer(5))),
        };
        
        let result = evaluator.evaluate(&expr);
        assert_eq!(result, Ok(LiteralValue::Integer(15)));
    }
    
    #[test]
    fn test_dynamic_pattern_matching() {
        let mut matcher = DynamicPatternMatcher::new();
        matcher.add_pattern(
            "test".to_string(),
            |expr| matches!(expr, ComplexExpression::Literal(_)),
            |_| Ok(LiteralValue::Integer(42)),
        );
        
        let expr = ComplexExpression::Literal(LiteralValue::Integer(10));
        let result = matcher.match_and_handle(&expr);
        assert_eq!(result, Ok(LiteralValue::Integer(42)));
    }
    
    #[test]
    fn test_pattern_optimization() {
        let mut optimizer = PatternMatchingOptimizer::new();
        let expr = ComplexExpression::BinaryOp {
            left: Box::new(ComplexExpression::Literal(LiteralValue::Integer(10))),
            operator: BinaryOperator::Add,
            right: Box::new(ComplexExpression::Literal(LiteralValue::Integer(20))),
        };
        
        let result = optimizer.evaluate_optimized(&expr);
        assert_eq!(result, Ok(LiteralValue::Integer(30)));
    }
    
    #[test]
    fn test_nested_pattern_matching() {
        let matcher = NestedPatternMatcher;
        let data = NestedData::Branch {
            name: "root".to_string(),
            children: vec![
                NestedData::Leaf("test".to_string()),
            ],
        };
        
        let found = matcher.find_by_name(&data, "test");
        assert_eq!(found.len(), 1);
    }
}
