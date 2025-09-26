//! 类型系统验证工具模块
//!
//! 本模块展示了 Rust 1.90 中的类型系统验证特性，包括：
//! - 类型约束验证
//! - 生命周期验证
//! - 泛型类型验证
//! - 类型转换验证
//! - 类型安全检查
//! - 类型推断验证
//!
//! # 文件信息
//! - 文件: type_system_validator.rs
//! - 创建日期: 2025-01-27
//! - 版本: 1.0
//! - Rust版本: 1.90.0
//! - Edition: 2024

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// ==================== 1. 类型系统基础 ====================

/// 类型表示
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// 基础类型
    Primitive(PrimitiveType),
    /// 复合类型
    Composite(CompositeType),
    /// 泛型类型
    Generic(GenericType),
    /// 函数类型
    Function(FunctionType),
    /// 引用类型
    Reference(ReferenceType),
    /// 生命周期类型
    Lifetime(LifetimeType),
    /// 未知类型
    Unknown,
}

/// 基础类型
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PrimitiveType {
    I8, I16, I32, I64, I128, Isize,
    U8, U16, U32, U64, U128, Usize,
    F32, F64,
    Bool, Char, String,
    Unit,
}

/// 复合类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompositeType {
    /// 元组类型
    Tuple(Vec<Type>),
    /// 数组类型
    Array { element: Box<Type>, size: Option<usize> },
    /// 切片类型
    Slice(Box<Type>),
    /// 结构体类型
    Struct { name: String, fields: HashMap<String, Type> },
    /// 枚举类型
    Enum { name: String, variants: HashMap<String, Vec<Type>> },
}

/// 泛型类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericType {
    pub name: String,
    pub parameters: Vec<Type>,
    pub constraints: Vec<TypeConstraint>,
}

/// 函数类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub parameters: Vec<Type>,
    pub return_type: Box<Type>,
    pub lifetime_params: Vec<LifetimeType>,
}

/// 引用类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReferenceType {
    pub lifetime: Option<LifetimeType>,
    pub mutable: bool,
    pub target: Box<Type>,
}

/// 生命周期类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LifetimeType {
    pub name: String,
    pub constraints: Vec<LifetimeType>,
}

/// 类型约束
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeConstraint {
    /// Trait 约束
    Trait(String),
    /// 生命周期约束
    Lifetime(LifetimeConstraint),
    /// 类型相等约束
    Equality(Type, Type),
    /// 类型包含约束
    Subtype(Type, Type),
}

/// 生命周期约束
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LifetimeConstraint {
    /// 生命周期包含
    Outlives(LifetimeType, LifetimeType),
    /// 生命周期相等
    Equals(LifetimeType, LifetimeType),
}

// ==================== 2. 类型验证器 ====================

/// 类型验证器
pub struct TypeValidator {
    /// 类型环境
    type_env: Arc<Mutex<TypeEnvironment>>,
    /// 验证规则
    validation_rules: Vec<ValidationRule>,
    /// 验证统计
    stats: Arc<Mutex<ValidationStats>>,
}

/// 类型环境
#[allow(dead_code)]
#[derive(Debug, Default)]
pub struct TypeEnvironment {
    /// 类型定义
    type_definitions: HashMap<String, Type>,
    /// 变量类型
    variable_types: HashMap<String, Type>,
    /// 生命周期定义
    lifetime_definitions: HashMap<String, LifetimeType>,
    /// 约束
    constraints: Vec<TypeConstraint>,
}

/// 验证规则
#[allow(dead_code)]
pub struct ValidationRule {
    pub name: String,
    pub description: String,
    pub validator: Box<dyn Fn(&Type, &TypeEnvironment) -> ValidationResult + Send + Sync>,
}

/// 验证结果
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct ValidationResult {
    pub valid: bool,
    pub message: String,
    pub suggestions: Vec<String>,
    pub severity: ValidationSeverity,
}

/// 验证严重程度
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(dead_code)]
pub enum ValidationSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

/// 验证统计
#[derive(Debug, Default)]
#[allow(dead_code)]
pub struct ValidationStats {
    pub total_validations: u64,
    pub successful_validations: u64,
    pub failed_validations: u64,
    pub validations_by_type: HashMap<String, u64>,
    pub validations_by_severity: HashMap<ValidationSeverity, u64>,
}

impl TypeValidator {
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self {
            type_env: Arc::new(Mutex::new(TypeEnvironment::default())),
            validation_rules: Vec::new(),
            stats: Arc::new(Mutex::new(ValidationStats::default())),
        }
    }
    
    /// 添加验证规则
    pub fn add_validation_rule<F>(&mut self, name: String, description: String, validator: F)
    where
        F: Fn(&Type, &TypeEnvironment) -> ValidationResult + Send + Sync + 'static,
    {
        self.validation_rules.push(ValidationRule {
            name,
            description,
            validator: Box::new(validator),
        });
    }
    
    /// 验证类型
    pub fn validate_type(&self, type_: &Type) -> Vec<ValidationResult> {
        let env = self.type_env.lock().unwrap();
        let mut results = Vec::new();
        
        for rule in &self.validation_rules {
            let result = (rule.validator)(type_, &env);
            results.push(result);
        }
        
        // 更新统计
        {
            let mut stats = self.stats.lock().unwrap();
            stats.total_validations += 1;
            
            let type_name = self.get_type_name(type_);
            *stats.validations_by_type.entry(type_name).or_insert(0) += 1;
            
            for result in &results {
                if result.valid {
                    stats.successful_validations += 1;
                } else {
                    stats.failed_validations += 1;
                }
                *stats.validations_by_severity.entry(result.severity).or_insert(0) += 1;
            }
        }
        
        results
    }
    
    /// 验证类型兼容性
    #[allow(unused_variables)]
    pub fn validate_compatibility(&self, from: &Type, to: &Type) -> ValidationResult {
        let env = self.type_env.lock().unwrap();
        
        if self.types_equal(from, to) {
            return ValidationResult {
                valid: true,
                message: "Types are identical".to_string(),
                suggestions: Vec::new(),
                severity: ValidationSeverity::Info,
            };
        }
        
        if self.is_subtype(from, to) {
            return ValidationResult {
                valid: true,
                message: "Type is compatible".to_string(),
                suggestions: Vec::new(),
                severity: ValidationSeverity::Info,
            };
        }
        
        ValidationResult {
            valid: false,
            message: format!("Type {} is not compatible with {}", 
                           self.format_type(from), self.format_type(to)),
            suggestions: vec![
                "Consider using explicit type conversion".to_string(),
                "Check if the types have a common trait".to_string(),
            ],
            severity: ValidationSeverity::Error,
        }
    }
    
    /// 验证生命周期
    #[allow(unused_variables)]
    pub fn validate_lifetime(&self, lifetime: &LifetimeType) -> ValidationResult {
        let env = self.type_env.lock().unwrap();
        
        // 检查生命周期是否已定义
        if !env.lifetime_definitions.contains_key(&lifetime.name) {
            return ValidationResult {
                valid: false,
                message: format!("Lifetime '{}' is not defined", lifetime.name),
                suggestions: vec![
                    "Define the lifetime parameter".to_string(),
                    "Use an existing lifetime".to_string(),
                ],
                severity: ValidationSeverity::Error,
            };
        }
        
        // 检查生命周期约束
        for constraint in &lifetime.constraints {
            if !self.validate_lifetime_constraint(&LifetimeConstraint::Outlives(constraint.clone(), constraint.clone()), &env) {
                return ValidationResult {
                    valid: false,
                    message: format!("Lifetime constraint violated for '{}'", lifetime.name),
                    suggestions: vec![
                        "Check lifetime bounds".to_string(),
                        "Consider using 'static lifetime".to_string(),
                    ],
                    severity: ValidationSeverity::Error,
                };
            }
        }
        
        ValidationResult {
            valid: true,
            message: "Lifetime is valid".to_string(),
            suggestions: Vec::new(),
            severity: ValidationSeverity::Info,
        }
    }
    
    /// 验证泛型类型
    pub fn validate_generic_type(&self, generic: &GenericType) -> ValidationResult {
        let env = self.type_env.lock().unwrap();
        
        // 检查泛型参数数量
        if generic.parameters.is_empty() {
            return ValidationResult {
                valid: false,
                message: format!("Generic type '{}' has no parameters", generic.name),
                suggestions: vec![
                    "Add type parameters".to_string(),
                    "Use a non-generic type".to_string(),
                ],
                severity: ValidationSeverity::Warning,
            };
        }
        
        // 验证每个参数
        for (i, param) in generic.parameters.iter().enumerate() {
            let param_results = self.validate_type(param);
            for result in param_results {
                if !result.valid {
                    return ValidationResult {
                        valid: false,
                        message: format!("Generic parameter {} is invalid: {}", i, result.message),
                        suggestions: result.suggestions,
                        severity: result.severity,
                    };
                }
            }
        }
        
        // 验证约束
        for constraint in &generic.constraints {
            if !self.validate_constraint(constraint, &env) {
                return ValidationResult {
                    valid: false,
                    message: "Generic constraint is not satisfied".to_string(),
                    suggestions: vec![
                        "Check trait bounds".to_string(),
                        "Verify lifetime constraints".to_string(),
                    ],
                    severity: ValidationSeverity::Error,
                };
            }
        }
        
        ValidationResult {
            valid: true,
            message: "Generic type is valid".to_string(),
            suggestions: Vec::new(),
            severity: ValidationSeverity::Info,
        }
    }
    
    /// 添加类型定义
    pub fn add_type_definition(&self, name: String, type_: Type) {
        let mut env = self.type_env.lock().unwrap();
        env.type_definitions.insert(name, type_);
    }
    
    /// 添加变量类型
    pub fn add_variable_type(&self, name: String, type_: Type) {
        let mut env = self.type_env.lock().unwrap();
        env.variable_types.insert(name, type_);
    }
    
    /// 添加生命周期定义
    pub fn add_lifetime_definition(&self, name: String, lifetime: LifetimeType) {
        let mut env = self.type_env.lock().unwrap();
        env.lifetime_definitions.insert(name, lifetime);
    }
    
    /// 获取验证统计
    pub fn get_stats(&self) -> ValidationStats {
        self.stats.lock().unwrap().clone()
    }
    
    /// 类型相等检查
    fn types_equal(&self, a: &Type, b: &Type) -> bool {
        match (a, b) {
            (Type::Primitive(pa), Type::Primitive(pb)) => pa == pb,
            (Type::Composite(ca), Type::Composite(cb)) => ca == cb,
            (Type::Generic(ga), Type::Generic(gb)) => ga == gb,
            (Type::Function(fa), Type::Function(fb)) => fa == fb,
            (Type::Reference(ra), Type::Reference(rb)) => ra == rb,
            (Type::Lifetime(la), Type::Lifetime(lb)) => la == lb,
            _ => false,
        }
    }
    
    /// 子类型检查
    fn is_subtype(&self, from: &Type, to: &Type) -> bool {
        // 简化实现，实际中需要更复杂的子类型关系
        match (from, to) {
            (Type::Primitive(PrimitiveType::I8), Type::Primitive(PrimitiveType::I32)) => true,
            (Type::Primitive(PrimitiveType::I16), Type::Primitive(PrimitiveType::I32)) => true,
            (Type::Primitive(PrimitiveType::I32), Type::Primitive(PrimitiveType::I64)) => true,
            _ => false,
        }
    }
    
    /// 验证生命周期约束
    fn validate_lifetime_constraint(&self, constraint: &LifetimeConstraint, _env: &TypeEnvironment) -> bool {
        // 简化实现
        match constraint {
            LifetimeConstraint::Outlives(_, _) => true,
            LifetimeConstraint::Equals(_, _) => true,
        }
    }
    
    /// 验证约束
    fn validate_constraint(&self, constraint: &TypeConstraint, _env: &TypeEnvironment) -> bool {
        // 简化实现
        match constraint {
            TypeConstraint::Trait(_) => true,
            TypeConstraint::Lifetime(_) => true,
            TypeConstraint::Equality(_, _) => true,
            TypeConstraint::Subtype(_, _) => true,
        }
    }
    
    /// 获取类型名称
    fn get_type_name(&self, type_: &Type) -> String {
        match type_ {
            Type::Primitive(p) => format!("Primitive({:?})", p),
            Type::Composite(c) => format!("Composite({:?})", c),
            Type::Generic(g) => format!("Generic({})", g.name),
            Type::Function(_) => "Function".to_string(),
            Type::Reference(_) => "Reference".to_string(),
            Type::Lifetime(l) => format!("Lifetime({})", l.name),
            Type::Unknown => "Unknown".to_string(),
        }
    }
    
    /// 格式化类型
    fn format_type(&self, type_: &Type) -> String {
        match type_ {
            Type::Primitive(p) => format!("{:?}", p),
            Type::Composite(c) => format!("{:?}", c),
            Type::Generic(g) => format!("{}<{}>", g.name, 
                g.parameters.iter().map(|p| self.format_type(p)).collect::<Vec<_>>().join(", ")),
            Type::Function(f) => format!("fn({}) -> {}", 
                f.parameters.iter().map(|p| self.format_type(p)).collect::<Vec<_>>().join(", "),
                self.format_type(&f.return_type)),
            Type::Reference(r) => {
                let lifetime = if let Some(l) = &r.lifetime {
                    format!("'{} ", l.name)
                } else {
                    String::new()
                };
                let mutability = if r.mutable { "mut " } else { "" };
                format!("&{}{}{}", lifetime, mutability, self.format_type(&r.target))
            },
            Type::Lifetime(l) => format!("'{}", l.name),
            Type::Unknown => "?".to_string(),
        }
    }
}

impl Default for TypeValidator {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for ValidationStats {
    fn clone(&self) -> Self {
        Self {
            total_validations: self.total_validations,
            successful_validations: self.successful_validations,
            failed_validations: self.failed_validations,
            validations_by_type: self.validations_by_type.clone(),
            validations_by_severity: self.validations_by_severity.clone(),
        }
    }
}

// ==================== 3. 类型推断器 ====================

/// 类型推断器
pub struct TypeInferencer {
    /// 类型环境
    type_env: Arc<Mutex<TypeEnvironment>>,
    /// 推断统计
    stats: Arc<Mutex<InferenceStats>>,
}

/// 推断统计
#[derive(Debug, Default)]
pub struct InferenceStats {
    pub total_inferences: u64,
    pub successful_inferences: u64,
    pub failed_inferences: u64,
    pub inferences_by_type: HashMap<String, u64>,
}

impl TypeInferencer {
    pub fn new() -> Self {
        Self {
            type_env: Arc::new(Mutex::new(TypeEnvironment::default())),
            stats: Arc::new(Mutex::new(InferenceStats::default())),
        }
    }
    
    /// 推断表达式类型
    pub fn infer_expression_type(&self, expression: &Expression) -> Result<Type, String> {
        match expression {
            Expression::Literal(lit) => Ok(self.infer_literal_type(lit)),
            Expression::Variable(name) => self.infer_variable_type(name),
            Expression::BinaryOp { left, operator, right } => {
                self.infer_binary_operation_type(left, operator, right)
            },
            Expression::UnaryOp { operator, operand } => {
                self.infer_unary_operation_type(operator, operand)
            },
            Expression::FunctionCall { name, arguments } => {
                self.infer_function_call_type(name, arguments)
            },
            Expression::If { condition, then_branch, else_branch } => {
                self.infer_if_expression_type(condition, then_branch, else_branch)
            },
        }
    }
    
    /// 推断字面量类型
    fn infer_literal_type(&self, literal: &Literal) -> Type {
        match literal {
            Literal::Integer(_) => Type::Primitive(PrimitiveType::I32),
            Literal::Float(_) => Type::Primitive(PrimitiveType::F64),
            Literal::Boolean(_) => Type::Primitive(PrimitiveType::Bool),
            Literal::String(_) => Type::Primitive(PrimitiveType::String),
            Literal::Char(_) => Type::Primitive(PrimitiveType::Char),
        }
    }
    
    /// 推断变量类型
    fn infer_variable_type(&self, name: &str) -> Result<Type, String> {
        let env = self.type_env.lock().unwrap();
        env.variable_types.get(name)
            .cloned()
            .ok_or_else(|| format!("Variable '{}' is not defined", name))
    }
    
    /// 推断二元操作类型
    fn infer_binary_operation_type(&self, left: &Expression, operator: &BinaryOperator, right: &Expression) -> Result<Type, String> {
        let left_type = self.infer_expression_type(left)?;
        let right_type = self.infer_expression_type(right)?;
        
        match operator {
            BinaryOperator::Add | BinaryOperator::Sub | BinaryOperator::Mul | BinaryOperator::Div => {
                self.infer_arithmetic_type(&left_type, &right_type)
            },
            BinaryOperator::Eq | BinaryOperator::Ne | BinaryOperator::Lt | BinaryOperator::Le | BinaryOperator::Gt | BinaryOperator::Ge => {
                Ok(Type::Primitive(PrimitiveType::Bool))
            },
            BinaryOperator::And | BinaryOperator::Or => {
                if self.types_compatible(&left_type, &Type::Primitive(PrimitiveType::Bool)) &&
                   self.types_compatible(&right_type, &Type::Primitive(PrimitiveType::Bool)) {
                    Ok(Type::Primitive(PrimitiveType::Bool))
                } else {
                    Err("Boolean operators require boolean operands".to_string())
                }
            },
        }
    }
    
    /// 推断一元操作类型
    fn infer_unary_operation_type(&self, operator: &UnaryOperator, operand: &Expression) -> Result<Type, String> {
        let operand_type = self.infer_expression_type(operand)?;
        
        match operator {
            UnaryOperator::Not => {
                if self.types_compatible(&operand_type, &Type::Primitive(PrimitiveType::Bool)) {
                    Ok(Type::Primitive(PrimitiveType::Bool))
                } else {
                    Err("Not operator requires boolean operand".to_string())
                }
            },
            UnaryOperator::Neg => {
                if self.is_numeric_type(&operand_type) {
                    Ok(operand_type)
                } else {
                    Err("Negation operator requires numeric operand".to_string())
                }
            },
        }
    }
    
    /// 推断函数调用类型
    fn infer_function_call_type(&self, name: &str, arguments: &[Expression]) -> Result<Type, String> {
        let env = self.type_env.lock().unwrap();
        
        if let Some(function_type) = env.type_definitions.get(name) {
            if let Type::Function(func_type) = function_type {
                // 验证参数数量
                if arguments.len() != func_type.parameters.len() {
                    return Err(format!("Function '{}' expects {} arguments, got {}", 
                                     name, func_type.parameters.len(), arguments.len()));
                }
                
                // 验证参数类型
                for (i, (arg, expected_type)) in arguments.iter().zip(func_type.parameters.iter()).enumerate() {
                    let arg_type = self.infer_expression_type(arg)?;
                    if !self.types_compatible(&arg_type, expected_type) {
                        return Err(format!("Argument {} of function '{}' has incompatible type", i, name));
                    }
                }
                
                Ok(*func_type.return_type.clone())
            } else {
                Err(format!("'{}' is not a function", name))
            }
        } else {
            Err(format!("Function '{}' is not defined", name))
        }
    }
    
    /// 推断 if 表达式类型
    fn infer_if_expression_type(&self, condition: &Expression, then_branch: &Expression, else_branch: &Expression) -> Result<Type, String> {
        let condition_type = self.infer_expression_type(condition)?;
        if !self.types_compatible(&condition_type, &Type::Primitive(PrimitiveType::Bool)) {
            return Err("If condition must be boolean".to_string());
        }
        
        let then_type = self.infer_expression_type(then_branch)?;
        let else_type = self.infer_expression_type(else_branch)?;
        
        if self.types_compatible(&then_type, &else_type) {
            Ok(then_type)
        } else {
            Err("If branches must have compatible types".to_string())
        }
    }
    
    /// 推断算术类型
    fn infer_arithmetic_type(&self, left: &Type, right: &Type) -> Result<Type, String> {
        match (left, right) {
            (Type::Primitive(PrimitiveType::I32), Type::Primitive(PrimitiveType::I32)) => {
                Ok(Type::Primitive(PrimitiveType::I32))
            },
            (Type::Primitive(PrimitiveType::F64), Type::Primitive(PrimitiveType::F64)) => {
                Ok(Type::Primitive(PrimitiveType::F64))
            },
            (Type::Primitive(PrimitiveType::I32), Type::Primitive(PrimitiveType::F64)) => {
                Ok(Type::Primitive(PrimitiveType::F64))
            },
            (Type::Primitive(PrimitiveType::F64), Type::Primitive(PrimitiveType::I32)) => {
                Ok(Type::Primitive(PrimitiveType::F64))
            },
            _ => Err("Arithmetic operations require numeric types".to_string()),
        }
    }
    
    /// 检查类型兼容性
    fn types_compatible(&self, from: &Type, to: &Type) -> bool {
        if from == to {
            return true;
        }
        
        // 简化实现
        match (from, to) {
            (Type::Primitive(PrimitiveType::I32), Type::Primitive(PrimitiveType::F64)) => true,
            (Type::Primitive(PrimitiveType::F64), Type::Primitive(PrimitiveType::I32)) => true,
            _ => false,
        }
    }
    
    /// 检查是否为数值类型
    fn is_numeric_type(&self, type_: &Type) -> bool {
        matches!(type_, Type::Primitive(PrimitiveType::I32 | PrimitiveType::F64))
    }
    
    /// 添加类型定义
    pub fn add_type_definition(&self, name: String, type_: Type) {
        let mut env = self.type_env.lock().unwrap();
        env.type_definitions.insert(name, type_);
    }
    
    /// 添加变量类型
    pub fn add_variable_type(&self, name: String, type_: Type) {
        let mut env = self.type_env.lock().unwrap();
        env.variable_types.insert(name, type_);
    }
    
    /// 获取推断统计
    pub fn get_stats(&self) -> InferenceStats {
        self.stats.lock().unwrap().clone()
    }
}

impl Default for TypeInferencer {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for InferenceStats {
    fn clone(&self) -> Self {
        Self {
            total_inferences: self.total_inferences,
            successful_inferences: self.successful_inferences,
            failed_inferences: self.failed_inferences,
            inferences_by_type: self.inferences_by_type.clone(),
        }
    }
}

// ==================== 4. 表达式和操作符 ====================

/// 表达式
#[derive(Debug, Clone)]
pub enum Expression {
    Literal(Literal),
    Variable(String),
    BinaryOp { left: Box<Expression>, operator: BinaryOperator, right: Box<Expression> },
    UnaryOp { operator: UnaryOperator, operand: Box<Expression> },
    FunctionCall { name: String, arguments: Vec<Expression> },
    If { condition: Box<Expression>, then_branch: Box<Expression>, else_branch: Box<Expression> },
}

/// 字面量
#[derive(Debug, Clone)]
pub enum Literal {
    Integer(i64),
    Float(f64),
    Boolean(bool),
    String(String),
    Char(char),
}

/// 二元操作符
#[derive(Debug, Clone, Copy)]
pub enum BinaryOperator {
    Add, Sub, Mul, Div,
    Eq, Ne, Lt, Le, Gt, Ge,
    And, Or,
}

/// 一元操作符
#[derive(Debug, Clone, Copy)]
pub enum UnaryOperator {
    Not, Neg,
}

// ==================== 演示函数 ====================

/// 演示所有类型系统验证特性
#[allow(unused_variables)]
pub fn demonstrate_type_system_validation() {
    println!("=== 类型系统验证演示 ===\n");
    
    // 1. 类型验证器演示
    println!("1. 类型验证器演示:");
    let mut validator = TypeValidator::new();
    
    // 添加验证规则
    validator.add_validation_rule(
        "primitive_type_validation".to_string(),
        "验证基础类型".to_string(),
        |type_, _env| {
            match type_ {
                Type::Primitive(_) => ValidationResult {
                    valid: true,
                    message: "Primitive type is valid".to_string(),
                    suggestions: Vec::new(),
                    severity: ValidationSeverity::Info,
                },
                _ => ValidationResult {
                    valid: false,
                    message: "Expected primitive type".to_string(),
                    suggestions: vec!["Use a primitive type".to_string()],
                    severity: ValidationSeverity::Warning,
                },
            }
        },
    );
    
    validator.add_validation_rule(
        "generic_type_validation".to_string(),
        "验证泛型类型".to_string(),
        |type_, _env| {
            match type_ {
                Type::Generic(generic) => {
                    if generic.parameters.is_empty() {
                        ValidationResult {
                            valid: false,
                            message: "Generic type has no parameters".to_string(),
                            suggestions: vec!["Add type parameters".to_string()],
                            severity: ValidationSeverity::Error,
                        }
                    } else {
                        ValidationResult {
                            valid: true,
                            message: "Generic type is valid".to_string(),
                            suggestions: Vec::new(),
                            severity: ValidationSeverity::Info,
                        }
                    }
                },
                _ => ValidationResult {
                    valid: true,
                    message: "Not a generic type".to_string(),
                    suggestions: Vec::new(),
                    severity: ValidationSeverity::Info,
                },
            }
        },
    );
    
    // 测试各种类型
    let test_types = vec![
        ("整数类型", Type::Primitive(PrimitiveType::I32)),
        ("浮点类型", Type::Primitive(PrimitiveType::F64)),
        ("布尔类型", Type::Primitive(PrimitiveType::Bool)),
        ("空泛型", Type::Generic(GenericType {
            name: "Vec".to_string(),
            parameters: Vec::new(),
            constraints: Vec::new(),
        })),
        ("有效泛型", Type::Generic(GenericType {
            name: "Vec".to_string(),
            parameters: vec![Type::Primitive(PrimitiveType::I32)],
            constraints: Vec::new(),
        })),
    ];
    
    for (type_name, type_) in test_types {
        println!("  验证 {}:", type_name);
        let results = validator.validate_type(&type_);
        for result in results {
            let status = if result.valid { "✅" } else { "❌" };
            println!("    {} {:?}: {}", status, result.severity, result.message);
            if !result.suggestions.is_empty() {
                for suggestion in result.suggestions {
                    println!("      建议: {}", suggestion);
                }
            }
        }
        println!();
    }
    
    // 2. 类型兼容性验证演示
    println!("2. 类型兼容性验证演示:");
    let compatibility_tests = vec![
        ("i32 -> i32", Type::Primitive(PrimitiveType::I32), Type::Primitive(PrimitiveType::I32)),
        ("i32 -> f64", Type::Primitive(PrimitiveType::I32), Type::Primitive(PrimitiveType::F64)),
        ("f64 -> i32", Type::Primitive(PrimitiveType::F64), Type::Primitive(PrimitiveType::I32)),
        ("bool -> i32", Type::Primitive(PrimitiveType::Bool), Type::Primitive(PrimitiveType::I32)),
    ];
    
    for (test_name, from, to) in compatibility_tests {
        let result = validator.validate_compatibility(&from, &to);
        let status = if result.valid { "✅" } else { "❌" };
        println!("  {} {}: {}", status, test_name, result.message);
    }
    println!();
    
    // 3. 生命周期验证演示
    println!("3. 生命周期验证演示:");
    let lifetime = LifetimeType {
        name: "a".to_string(),
        constraints: Vec::new(),
    };
    
    validator.add_lifetime_definition("a".to_string(), lifetime.clone());
    
    let result = validator.validate_lifetime(&lifetime);
    let status = if result.valid { "✅" } else { "❌" };
    println!("  {} 生命周期验证: {}", status, result.message);
    println!();
    
    // 4. 泛型类型验证演示
    println!("4. 泛型类型验证演示:");
    let generic_type = GenericType {
        name: "HashMap".to_string(),
        parameters: vec![
            Type::Primitive(PrimitiveType::String),
            Type::Primitive(PrimitiveType::I32),
        ],
        constraints: Vec::new(),
    };
    
    let result = validator.validate_generic_type(&generic_type);
    let status = if result.valid { "✅" } else { "❌" };
    println!("  {} 泛型类型验证: {}", status, result.message);
    println!();
    
    // 5. 类型推断演示
    println!("5. 类型推断演示:");
    let inferencer = TypeInferencer::new();
    
    // 添加函数定义
    let add_function = Type::Function(FunctionType {
        parameters: vec![
            Type::Primitive(PrimitiveType::I32),
            Type::Primitive(PrimitiveType::I32),
        ],
        return_type: Box::new(Type::Primitive(PrimitiveType::I32)),
        lifetime_params: Vec::new(),
    });
    
    inferencer.add_type_definition("add".to_string(), add_function);
    
    // 测试表达式推断
    let expressions = vec![
        ("字面量", Expression::Literal(Literal::Integer(42))),
        ("二元操作", Expression::BinaryOp {
            left: Box::new(Expression::Literal(Literal::Integer(10))),
            operator: BinaryOperator::Add,
            right: Box::new(Expression::Literal(Literal::Integer(20))),
        }),
        ("函数调用", Expression::FunctionCall {
            name: "add".to_string(),
            arguments: vec![
                Expression::Literal(Literal::Integer(5)),
                Expression::Literal(Literal::Integer(3)),
            ],
        }),
    ];
    
    for (expr_name, expr) in expressions {
        match inferencer.infer_expression_type(&expr) {
            Ok(type_) => println!("  ✅ {} 推断类型: {}", expr_name, validator.format_type(&type_)),
            Err(e) => println!("  ❌ {} 推断失败: {}", expr_name, e),
        }
    }
    println!();
    
    // 6. 验证统计演示
    println!("6. 验证统计演示:");
    let stats = validator.get_stats();
    println!("  总验证次数: {}", stats.total_validations);
    println!("  成功验证: {}", stats.successful_validations);
    println!("  失败验证: {}", stats.failed_validations);
    println!("  按类型分布: {:?}", stats.validations_by_type);
    println!("  按严重程度分布: {:?}", stats.validations_by_severity);
    
    let inference_stats = inferencer.get_stats();
    println!("  推断统计: {:?}", inference_stats);
    
    println!("\n=== 类型系统验证演示完成 ===");
}

// ==================== 测试模块 ====================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_type_validation() {
        let validator = TypeValidator::new();
        let int_type = Type::Primitive(PrimitiveType::I32);
        let results = validator.validate_type(&int_type);
        assert!(!results.is_empty());
    }
    
    #[test]
    fn test_type_compatibility() {
        let validator = TypeValidator::new();
        let from = Type::Primitive(PrimitiveType::I32);
        let to = Type::Primitive(PrimitiveType::I32);
        let result = validator.validate_compatibility(&from, &to);
        assert!(result.valid);
    }
    
    #[test]
    fn test_lifetime_validation() {
        let validator = TypeValidator::new();
        let lifetime = LifetimeType {
            name: "a".to_string(),
            constraints: Vec::new(),
        };
        validator.add_lifetime_definition("a".to_string(), lifetime.clone());
        let result = validator.validate_lifetime(&lifetime);
        assert!(result.valid);
    }
    
    #[test]
    fn test_type_inference() {
        let inferencer = TypeInferencer::new();
        let expr = Expression::Literal(Literal::Integer(42));
        let result = inferencer.infer_expression_type(&expr);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), Type::Primitive(PrimitiveType::I32));
    }
}
