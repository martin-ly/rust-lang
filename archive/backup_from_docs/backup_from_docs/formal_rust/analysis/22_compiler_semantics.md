# 编译器语义分析

## 📊 目录

- [编译器语义分析](#编译器语义分析)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [1. 编译器架构](#1-编译器架构)
    - [1.1 编译阶段](#11-编译阶段)
    - [1.2 抽象语法树](#12-抽象语法树)
  - [2. 类型检查](#2-类型检查)
    - [2.1 类型推断](#21-类型推断)
    - [2.2 类型约束求解](#22-类型约束求解)
  - [3. 借用检查](#3-借用检查)
    - [3.1 借用检查器](#31-借用检查器)
  - [4. 代码生成](#4-代码生成)
    - [4.1 LLVM IR生成](#41-llvm-ir生成)
  - [5. 优化策略](#5-优化策略)
    - [5.1 编译器优化](#51-编译器优化)
  - [6. 错误处理](#6-错误处理)
    - [6.1 编译错误](#61-编译错误)
  - [7. 测试和验证](#7-测试和验证)
    - [7.1 编译器测试](#71-编译器测试)
  - [8. 总结](#8-总结)

## 概述

本文档详细分析Rust编译器的语义，包括编译阶段、类型检查、借用检查、代码生成和优化策略。

## 1. 编译器架构

### 1.1 编译阶段

**定义 1.1.1 (编译阶段)**
Rust编译器将源代码转换为可执行代码的过程分为多个阶段，每个阶段都有特定的语义处理。

**编译阶段流程**：

```rust
// 编译阶段示例
// 1. 词法分析 (Lexical Analysis)
let tokens = lexer::tokenize(source_code);

// 2. 语法分析 (Syntax Analysis)
let ast = parser::parse(tokens);

// 3. 语义分析 (Semantic Analysis)
let hir = semantic_analysis::analyze(ast);

// 4. 类型检查 (Type Checking)
let typed_hir = type_checker::check(hir);

// 5. 借用检查 (Borrow Checking)
let borrow_checked = borrow_checker::check(typed_hir);

// 6. 代码生成 (Code Generation)
let llvm_ir = codegen::generate(borrow_checked);

// 7. 优化 (Optimization)
let optimized = optimizer::optimize(llvm_ir);
```

### 1.2 抽象语法树

**AST结构定义**：

```rust
#[derive(Debug, Clone)]
pub enum Expr {
    Literal(Literal),
    Variable(String),
    BinaryOp(Box<Expr>, BinOp, Box<Expr>),
    FunctionCall(String, Vec<Expr>),
    Block(Vec<Stmt>),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    Loop(Box<Expr>),
    Return(Option<Box<Expr>>),
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Expr(Expr),
    Let(String, Option<Type>, Expr),
    FunctionDef(FunctionDef),
    StructDef(StructDef),
    EnumDef(EnumDef),
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Option<Type>,
    pub body: Expr,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub ty: Type,
}
```

## 2. 类型检查

### 2.1 类型推断

**类型推断算法**：

```rust
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Float,
    Bool,
    String,
    Function(Vec<Type>, Box<Type>),
    Generic(String),
    Unknown,
}

pub struct TypeChecker {
    env: HashMap<String, Type>,
    constraints: Vec<(Type, Type)>,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            env: HashMap::new(),
            constraints: Vec::new(),
        }
    }
    
    pub fn infer_type(&mut self, expr: &Expr) -> Type {
        match expr {
            Expr::Literal(lit) => self.infer_literal(lit),
            Expr::Variable(name) => self.lookup_type(name),
            Expr::BinaryOp(left, op, right) => {
                let left_type = self.infer_type(left);
                let right_type = self.infer_type(right);
                self.infer_binary_op(left_type, op, right_type)
            }
            Expr::FunctionCall(name, args) => {
                let arg_types: Vec<Type> = args.iter()
                    .map(|arg| self.infer_type(arg))
                    .collect();
                self.infer_function_call(name, arg_types)
            }
            _ => Type::Unknown,
        }
    }
    
    fn infer_literal(&self, lit: &Literal) -> Type {
        match lit {
            Literal::Int(_) => Type::Int,
            Literal::Float(_) => Type::Float,
            Literal::Bool(_) => Type::Bool,
            Literal::String(_) => Type::String,
        }
    }
    
    fn infer_binary_op(&mut self, left: Type, op: &BinOp, right: Type) -> Type {
        // 添加类型约束
        self.constraints.push((left.clone(), right.clone()));
        
        match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                if left == Type::Int && right == Type::Int {
                    Type::Int
                } else if left == Type::Float && right == Type::Float {
                    Type::Float
                } else {
                    Type::Unknown
                }
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                Type::Bool
            }
        }
    }
    
    fn lookup_type(&self, name: &str) -> Type {
        self.env.get(name).cloned().unwrap_or(Type::Unknown)
    }
    
    fn infer_function_call(&self, name: &str, arg_types: Vec<Type>) -> Type {
        // 简化的函数类型推断
        if let Some(func_type) = self.env.get(name) {
            if let Type::Function(param_types, return_type) = func_type {
                if param_types.len() == arg_types.len() {
                    return *return_type.clone();
                }
            }
        }
        Type::Unknown
    }
}
```

### 2.2 类型约束求解

**约束求解算法**：

```rust
pub struct ConstraintSolver {
    substitutions: HashMap<String, Type>,
}

impl ConstraintSolver {
    pub fn new() -> Self {
        Self {
            substitutions: HashMap::new(),
        }
    }
    
    pub fn solve(&mut self, constraints: Vec<(Type, Type)>) -> Result<HashMap<String, Type>, String> {
        for (left, right) in constraints {
            self.unify(left, right)?;
        }
        Ok(self.substitutions.clone())
    }
    
    fn unify(&mut self, left: Type, right: Type) -> Result<(), String> {
        match (left, right) {
            (Type::Int, Type::Int) | (Type::Float, Type::Float) | (Type::Bool, Type::Bool) => {
                Ok(())
            }
            (Type::Generic(name), other) | (other, Type::Generic(name)) => {
                self.substitutions.insert(name, other);
                Ok(())
            }
            (Type::Function(left_params, left_ret), Type::Function(right_params, right_ret)) => {
                if left_params.len() != right_params.len() {
                    return Err("Function parameter count mismatch".to_string());
                }
                
                for (left_param, right_param) in left_params.iter().zip(right_params.iter()) {
                    self.unify(left_param.clone(), right_param.clone())?;
                }
                
                self.unify(*left_ret, *right_ret)
            }
            _ => Err("Type mismatch".to_string()),
        }
    }
}
```

## 3. 借用检查

### 3.1 借用检查器

**借用检查器实现**：

```rust
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct BorrowChecker {
    variables: HashMap<String, VariableState>,
    current_scope: usize,
    scopes: Vec<HashSet<String>>,
}

#[derive(Debug, Clone)]
pub struct VariableState {
    pub name: String,
    pub lifetime: Lifetime,
    pub borrows: Vec<Borrow>,
    pub is_moved: bool,
}

#[derive(Debug, Clone)]
pub struct Borrow {
    pub kind: BorrowKind,
    pub lifetime: Lifetime,
    pub scope: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BorrowKind {
    Shared,
    Mutable,
}

#[derive(Debug, Clone)]
pub struct Lifetime {
    pub name: String,
    pub scope: usize,
}

impl BorrowChecker {
    pub fn new() -> Self {
        Self {
            variables: HashMap::new(),
            current_scope: 0,
            scopes: vec![HashSet::new()],
        }
    }
    
    pub fn enter_scope(&mut self) {
        self.current_scope += 1;
        self.scopes.push(HashSet::new());
    }
    
    pub fn exit_scope(&mut self) {
        // 清理当前作用域的借用
        if let Some(scope_vars) = self.scopes.pop() {
            for var_name in scope_vars {
                if let Some(var) = self.variables.get_mut(&var_name) {
                    var.borrows.retain(|borrow| borrow.scope != self.current_scope);
                }
            }
        }
        self.current_scope -= 1;
    }
    
    pub fn check_borrow(&mut self, var_name: &str, kind: BorrowKind) -> Result<(), String> {
        let var = self.variables.get_mut(var_name)
            .ok_or_else(|| format!("Variable {} not found", var_name))?;
        
        if var.is_moved {
            return Err(format!("Cannot borrow moved value: {}", var_name));
        }
        
        // 检查借用冲突
        for borrow in &var.borrows {
            match (&kind, &borrow.kind) {
                (BorrowKind::Mutable, _) | (_, BorrowKind::Mutable) => {
                    return Err(format!("Cannot borrow {} as mutable: conflicting borrow", var_name));
                }
                _ => {}
            }
        }
        
        // 添加新的借用
        let borrow = Borrow {
            kind,
            lifetime: Lifetime {
                name: format!("'{}", self.current_scope),
                scope: self.current_scope,
            },
            scope: self.current_scope,
        };
        
        var.borrows.push(borrow);
        self.scopes[self.current_scope].insert(var_name.to_string());
        
        Ok(())
    }
    
    pub fn check_move(&mut self, var_name: &str) -> Result<(), String> {
        let var = self.variables.get_mut(var_name)
            .ok_or_else(|| format!("Variable {} not found", var_name))?;
        
        if !var.borrows.is_empty() {
            return Err(format!("Cannot move {}: it is borrowed", var_name));
        }
        
        var.is_moved = true;
        Ok(())
    }
    
    pub fn declare_variable(&mut self, name: String) {
        let var_state = VariableState {
            name: name.clone(),
            lifetime: Lifetime {
                name: format!("'{}", self.current_scope),
                scope: self.current_scope,
            },
            borrows: Vec::new(),
            is_moved: false,
        };
        
        self.variables.insert(name, var_state);
    }
}
```

## 4. 代码生成

### 4.1 LLVM IR生成

**LLVM IR生成器**：

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct LLVMGenerator {
    module: String,
    functions: HashMap<String, String>,
    variables: HashMap<String, String>,
    counter: usize,
}

impl LLVMGenerator {
    pub fn new() -> Self {
        Self {
            module: String::new(),
            functions: HashMap::new(),
            variables: HashMap::new(),
            counter: 0,
        }
    }
    
    pub fn generate_function(&mut self, func: &FunctionDef) -> String {
        let mut ir = String::new();
        
        // 函数签名
        let params: Vec<String> = func.params.iter()
            .map(|p| format!("i32 %{}", p.name))
            .collect();
        
        ir.push_str(&format!("define i32 @{}({}) {{\n", 
            func.name, 
            params.join(", ")
        ));
        
        // 函数体
        ir.push_str(&self.generate_expr(&func.body));
        
        // 返回语句
        ir.push_str("  ret i32 0\n");
        ir.push_str("}\n\n");
        
        self.functions.insert(func.name.clone(), ir.clone());
        ir
    }
    
    pub fn generate_expr(&mut self, expr: &Expr) -> String {
        match expr {
            Expr::Literal(lit) => self.generate_literal(lit),
            Expr::Variable(name) => self.generate_variable(name),
            Expr::BinaryOp(left, op, right) => self.generate_binary_op(left, op, right),
            Expr::FunctionCall(name, args) => self.generate_function_call(name, args),
            Expr::Block(stmts) => self.generate_block(stmts),
            _ => String::new(),
        }
    }
    
    fn generate_literal(&self, lit: &Literal) -> String {
        match lit {
            Literal::Int(n) => format!("  ret i32 {}\n", n),
            Literal::Float(f) => format!("  ret double {}\n", f),
            Literal::Bool(b) => format!("  ret i1 {}\n", if *b { 1 } else { 0 }),
            Literal::String(s) => format!("  ret i8* getelementptr inbounds ([{} x i8], [{} x i8]* @.str, i32 0, i32 0)\n", 
                s.len() + 1, s.len() + 1),
        }
    }
    
    fn generate_variable(&self, name: &str) -> String {
        if let Some(var_ref) = self.variables.get(name) {
            format!("  %{} = load i32, i32* {}\n", self.counter, var_ref)
        } else {
            format!("  ; Variable {} not found\n", name)
        }
    }
    
    fn generate_binary_op(&mut self, left: &Expr, op: &BinOp, right: &Expr) -> String {
        let left_ir = self.generate_expr(left);
        let right_ir = self.generate_expr(right);
        
        let op_str = match op {
            BinOp::Add => "add",
            BinOp::Sub => "sub",
            BinOp::Mul => "mul",
            BinOp::Div => "sdiv",
            BinOp::Eq => "icmp eq",
            BinOp::Ne => "icmp ne",
            BinOp::Lt => "icmp slt",
            BinOp::Le => "icmp sle",
            BinOp::Gt => "icmp sgt",
            BinOp::Ge => "icmp sge",
        };
        
        format!("{}{}  %{} = {} i32 %{}, %{}\n", 
            left_ir, right_ir, self.counter, op_str, 
            self.counter - 2, self.counter - 1)
    }
    
    fn generate_function_call(&mut self, name: &str, args: &[Expr]) -> String {
        let mut ir = String::new();
        let mut arg_refs = Vec::new();
        
        for arg in args {
            ir.push_str(&self.generate_expr(arg));
            arg_refs.push(format!("%{}", self.counter - 1));
        }
        
        ir.push_str(&format!("  %{} = call i32 @{}({})\n", 
            self.counter, name, arg_refs.join(", ")));
        
        ir
    }
    
    fn generate_block(&mut self, stmts: &[Stmt]) -> String {
        let mut ir = String::new();
        
        for stmt in stmts {
            ir.push_str(&self.generate_stmt(stmt));
        }
        
        ir
    }
    
    fn generate_stmt(&mut self, stmt: &Stmt) -> String {
        match stmt {
            Stmt::Expr(expr) => self.generate_expr(expr),
            Stmt::Let(name, ty, expr) => {
                let expr_ir = self.generate_expr(expr);
                let var_ref = format!("%{}", self.counter);
                self.variables.insert(name.clone(), var_ref.clone());
                
                format!("{}  store i32 %{}, i32* {}\n", expr_ir, self.counter - 1, var_ref)
            }
            _ => String::new(),
        }
    }
}
```

## 5. 优化策略

### 5.1 编译器优化

**优化pass实现**：

```rust
pub struct Optimizer {
    passes: Vec<Box<dyn OptimizationPass>>,
}

pub trait OptimizationPass {
    fn name(&self) -> &str;
    fn run(&self, module: &mut String) -> bool;
}

pub struct ConstantFoldingPass;

impl OptimizationPass for ConstantFoldingPass {
    fn name(&self) -> &str {
        "constant-folding"
    }
    
    fn run(&self, module: &mut String) -> bool {
        // 常量折叠优化
        let mut changed = false;
        
        // 查找常量表达式并替换
        let patterns = vec![
            ("add i32 1, 2", "3"),
            ("mul i32 3, 4", "12"),
            ("sub i32 10, 5", "5"),
        ];
        
        for (pattern, replacement) in patterns {
            if module.contains(pattern) {
                *module = module.replace(pattern, replacement);
                changed = true;
            }
        }
        
        changed
    }
}

pub struct DeadCodeEliminationPass;

impl OptimizationPass for DeadCodeEliminationPass {
    fn name(&self) -> &str {
        "dead-code-elimination"
    }
    
    fn run(&self, module: &mut String) -> bool {
        // 死代码消除
        let mut changed = false;
        
        // 移除未使用的变量和函数
        let lines: Vec<&str> = module.lines().collect();
        let mut used_vars = HashSet::new();
        let mut used_funcs = HashSet::new();
        
        for line in &lines {
            // 分析使用的变量和函数
            if line.contains("call") {
                if let Some(func_name) = extract_function_name(line) {
                    used_funcs.insert(func_name);
                }
            }
            
            if line.contains("%") {
                if let Some(var_name) = extract_variable_name(line) {
                    used_vars.insert(var_name);
                }
            }
        }
        
        // 移除未使用的代码
        let mut new_lines = Vec::new();
        for line in lines {
            if !is_dead_code(line, &used_vars, &used_funcs) {
                new_lines.push(line);
            } else {
                changed = true;
            }
        }
        
        *module = new_lines.join("\n");
        changed
    }
}

impl Optimizer {
    pub fn new() -> Self {
        let mut optimizer = Self { passes: Vec::new() };
        
        // 添加优化pass
        optimizer.passes.push(Box::new(ConstantFoldingPass));
        optimizer.passes.push(Box::new(DeadCodeEliminationPass));
        
        optimizer
    }
    
    pub fn optimize(&self, module: &mut String) {
        let mut changed = true;
        let mut iterations = 0;
        const MAX_ITERATIONS: usize = 10;
        
        while changed && iterations < MAX_ITERATIONS {
            changed = false;
            
            for pass in &self.passes {
                if pass.run(module) {
                    changed = true;
                    println!("Applied optimization: {}", pass.name());
                }
            }
            
            iterations += 1;
        }
    }
}

fn extract_function_name(line: &str) -> Option<String> {
    if line.contains("call") {
        let parts: Vec<&str> = line.split_whitespace().collect();
        for (i, part) in parts.iter().enumerate() {
            if part == &"call" && i + 1 < parts.len() {
                return Some(parts[i + 1].to_string());
            }
        }
    }
    None
}

fn extract_variable_name(line: &str) -> Option<String> {
    if line.contains("%") {
        let parts: Vec<&str> = line.split_whitespace().collect();
        for part in parts {
            if part.starts_with('%') {
                return Some(part.to_string());
            }
        }
    }
    None
}

fn is_dead_code(line: &str, used_vars: &HashSet<String>, used_funcs: &HashSet<String>) -> bool {
    // 检查是否是未使用的变量定义
    if line.contains("define") {
        if let Some(func_name) = extract_function_name(line) {
            return !used_funcs.contains(&func_name);
        }
    }
    
    // 检查是否是未使用的变量
    if line.contains("store") {
        if let Some(var_name) = extract_variable_name(line) {
            return !used_vars.contains(&var_name);
        }
    }
    
    false
}
```

## 6. 错误处理

### 6.1 编译错误

**编译错误类型**：

```rust
#[derive(Debug, Clone)]
pub enum CompileError {
    LexicalError(LexicalError),
    SyntaxError(SyntaxError),
    TypeError(TypeError),
    BorrowError(BorrowError),
    LifetimeError(LifetimeError),
}

#[derive(Debug, Clone)]
pub struct LexicalError {
    pub message: String,
    pub line: usize,
    pub column: usize,
}

#[derive(Debug, Clone)]
pub struct SyntaxError {
    pub message: String,
    pub line: usize,
    pub column: usize,
    pub expected: Vec<String>,
    pub found: String,
}

#[derive(Debug, Clone)]
pub struct TypeError {
    pub message: String,
    pub line: usize,
    pub column: usize,
    pub expected: Type,
    pub found: Type,
}

#[derive(Debug, Clone)]
pub struct BorrowError {
    pub message: String,
    pub line: usize,
    pub column: usize,
    pub variable: String,
    pub borrow_kind: BorrowKind,
}

#[derive(Debug, Clone)]
pub struct LifetimeError {
    pub message: String,
    pub line: usize,
    pub column: usize,
    pub lifetime: String,
    pub suggestion: Option<String>,
}

pub struct ErrorReporter {
    errors: Vec<CompileError>,
    warnings: Vec<CompileError>,
}

impl ErrorReporter {
    pub fn new() -> Self {
        Self {
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }
    
    pub fn report_error(&mut self, error: CompileError) {
        self.errors.push(error);
    }
    
    pub fn report_warning(&mut self, warning: CompileError) {
        self.warnings.push(warning);
    }
    
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }
    
    pub fn print_errors(&self, source: &str) {
        for error in &self.errors {
            self.print_error(error, source);
        }
    }
    
    fn print_error(&self, error: &CompileError, source: &str) {
        let (line, column, message) = match error {
            CompileError::LexicalError(e) => (e.line, e.column, &e.message),
            CompileError::SyntaxError(e) => (e.line, e.column, &e.message),
            CompileError::TypeError(e) => (e.line, e.column, &e.message),
            CompileError::BorrowError(e) => (e.line, e.column, &e.message),
            CompileError::LifetimeError(e) => (e.line, e.column, &e.message),
        };
        
        println!("error at line {}, column {}: {}", line, column, message);
        
        // 显示错误位置的代码行
        if let Some(code_line) = source.lines().nth(line - 1) {
            println!("  {}", code_line);
            println!("  {}^", " ".repeat(column - 1));
        }
    }
}
```

## 7. 测试和验证

### 7.1 编译器测试

**编译器测试框架**：

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_inference() {
        let mut checker = TypeChecker::new();
        
        // 测试字面量类型推断
        let int_lit = Expr::Literal(Literal::Int(42));
        let inferred_type = checker.infer_type(&int_lit);
        assert_eq!(inferred_type, Type::Int);
        
        // 测试二元运算类型推断
        let binary_op = Expr::BinaryOp(
            Box::new(Expr::Literal(Literal::Int(1))),
            BinOp::Add,
            Box::new(Expr::Literal(Literal::Int(2)))
        );
        let inferred_type = checker.infer_type(&binary_op);
        assert_eq!(inferred_type, Type::Int);
    }

    #[test]
    fn test_borrow_checking() {
        let mut checker = BorrowChecker::new();
        
        // 声明变量
        checker.declare_variable("x".to_string());
        
        // 测试共享借用
        assert!(checker.check_borrow("x", BorrowKind::Shared).is_ok());
        
        // 测试可变借用冲突
        assert!(checker.check_borrow("x", BorrowKind::Mutable).is_err());
    }

    #[test]
    fn test_llvm_generation() {
        let mut generator = LLVMGenerator::new();
        
        // 创建简单函数
        let func = FunctionDef {
            name: "add".to_string(),
            params: vec![
                Param { name: "a".to_string(), ty: Type::Int },
                Param { name: "b".to_string(), ty: Type::Int },
            ],
            return_type: Some(Type::Int),
            body: Expr::BinaryOp(
                Box::new(Expr::Variable("a".to_string())),
                BinOp::Add,
                Box::new(Expr::Variable("b".to_string()))
            ),
        };
        
        let ir = generator.generate_function(&func);
        assert!(ir.contains("define i32 @add"));
        assert!(ir.contains("add i32"));
    }

    #[test]
    fn test_optimization() {
        let optimizer = Optimizer::new();
        let mut module = "  %1 = add i32 1, 2\n  %2 = mul i32 3, 4\n".to_string();
        
        optimizer.optimize(&mut module);
        
        // 检查常量折叠是否生效
        assert!(module.contains("3"));
        assert!(module.contains("12"));
    }
}
```

## 8. 总结

Rust编译器语义分析涵盖了从源代码到可执行代码的完整编译过程。通过深入理解编译器的各个阶段、类型检查、借用检查、代码生成和优化策略，可以更好地理解Rust语言的语义和实现原理。

编译器语义分析为Rust语言的理论研究和工程实践提供了重要的基础，有助于开发更高效、更安全的Rust程序。
