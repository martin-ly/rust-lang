//! WebAssembly编译流水线案例
//! 
//! 本模块演示Rust到WebAssembly的完整编译流水线，包括词法分析、语法分析、语义分析、代码生成等阶段。
//! 
//! 理论映射：
//! - 编译函数: C: Rust → WebAssembly
//! - 类型映射: types: RustTypes → WasmTypes
//! - 语义等价: semantics(P_Rust) ≡ semantics(C(P_Rust))
//! - 安全保持: safe(P_Rust) ⇒ safe(C(P_Rust))

use std::collections::HashMap;
use serde::{Deserialize, Serialize};

/// WebAssembly编译流水线
/// 
/// 理论映射: C: Rust → WebAssembly
pub struct CompilationPipeline {
    pub lexer: Lexer,
    pub parser: Parser,
    pub semantic_analyzer: SemanticAnalyzer,
    pub code_generator: CodeGenerator,
    pub optimizer: Optimizer,
}

impl CompilationPipeline {
    pub fn new() -> Self {
        Self {
            lexer: Lexer::new(),
            parser: Parser::new(),
            semantic_analyzer: SemanticAnalyzer::new(),
            code_generator: CodeGenerator::new(),
            optimizer: Optimizer::new(),
        }
    }
    
    /// 执行完整编译流水线
    /// 
    /// 理论映射: C(P_Rust) = optimize ∘ generate ∘ analyze ∘ parse ∘ lex(P_Rust)
    pub fn compile(&self, source_code: &str) -> Result<WasmModule, CompilationError> {
        // 1. 词法分析
        let tokens = self.lexer.tokenize(source_code)?;
        
        // 2. 语法分析
        let ast = self.parser.parse(&tokens)?;
        
        // 3. 语义分析
        let semantic_info = self.semantic_analyzer.analyze(&ast)?;
        
        // 4. 代码生成
        let wasm_module = self.code_generator.generate(&ast, &semantic_info)?;
        
        // 5. 优化
        let optimized_module = self.optimizer.optimize(wasm_module)?;
        
        Ok(optimized_module)
    }
    
    /// 验证编译正确性
    /// 
    /// 理论映射: semantics(P_Rust) ≡ semantics(C(P_Rust))
    pub fn verify_correctness(&self, rust_program: &str, wasm_module: &WasmModule) -> bool {
        // 简化验证：检查基本属性
        let has_functions = !wasm_module.functions.is_empty();
        let has_valid_types = wasm_module.types.iter().all(|t| self.is_valid_type(t));
        let has_valid_memory = wasm_module.memories.iter().all(|m| self.is_valid_memory(m));
        
        has_functions && has_valid_types && has_valid_memory
    }
    
    fn is_valid_type(&self, func_type: &FuncType) -> bool {
        // 检查函数类型是否有效
        !func_type.params.is_empty() || !func_type.results.is_empty()
    }
    
    fn is_valid_memory(&self, memory: &Memory) -> bool {
        // 检查内存定义是否有效
        memory.limits.initial > 0 && memory.limits.initial <= memory.limits.maximum
    }
}

/// 词法分析器
/// 
/// 理论映射: lex: SourceCode → Tokens
pub struct Lexer {
    pub keywords: HashMap<String, TokenType>,
}

impl Lexer {
    pub fn new() -> Self {
        let mut keywords = HashMap::new();
        keywords.insert("fn".to_string(), TokenType::Function);
        keywords.insert("let".to_string(), TokenType::Let);
        keywords.insert("mut".to_string(), TokenType::Mut);
        keywords.insert("return".to_string(), TokenType::Return);
        keywords.insert("if".to_string(), TokenType::If);
        keywords.insert("else".to_string(), TokenType::Else);
        keywords.insert("for".to_string(), TokenType::For);
        keywords.insert("while".to_string(), TokenType::While);
        
        Self { keywords }
    }
    
    /// 词法分析
    /// 
    /// 理论映射: tokenize: String → [Token]
    pub fn tokenize(&self, source: &str) -> Result<Vec<Token>, CompilationError> {
        let mut tokens = Vec::new();
        let mut chars = source.chars().peekable();
        
        while let Some(&ch) = chars.peek() {
            match ch {
                'a'..='z' | 'A'..='Z' | '_' => {
                    let identifier = self.read_identifier(&mut chars);
                    let token_type = self.keywords.get(&identifier)
                        .unwrap_or(&TokenType::Identifier)
                        .clone();
                    tokens.push(Token {
                        token_type,
                        value: identifier,
                        line: 1, // 简化行号
                    });
                }
                '0'..='9' => {
                    let number = self.read_number(&mut chars);
                    tokens.push(Token {
                        token_type: TokenType::Number,
                        value: number,
                        line: 1,
                    });
                }
                '+' | '-' | '*' | '/' => {
                    let operator = chars.next().unwrap().to_string();
                    tokens.push(Token {
                        token_type: TokenType::Operator,
                        value: operator,
                        line: 1,
                    });
                }
                '(' | ')' | '{' | '}' | ';' | ',' => {
                    let punctuation = chars.next().unwrap().to_string();
                    tokens.push(Token {
                        token_type: TokenType::Punctuation,
                        value: punctuation,
                        line: 1,
                    });
                }
                ' ' | '\t' | '\n' => {
                    chars.next(); // 跳过空白字符
                }
                _ => {
                    return Err(CompilationError::LexicalError(format!("Unexpected character: {}", ch)));
                }
            }
        }
        
        Ok(tokens)
    }
    
    fn read_identifier(&self, chars: &mut std::iter::Peekable<std::str::Chars>) -> String {
        let mut identifier = String::new();
        while let Some(&ch) = chars.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                identifier.push(chars.next().unwrap());
            } else {
                break;
            }
        }
        identifier
    }
    
    fn read_number(&self, chars: &mut std::iter::Peekable<std::str::Chars>) -> String {
        let mut number = String::new();
        while let Some(&ch) = chars.peek() {
            if ch.is_digit(10) || ch == '.' {
                number.push(chars.next().unwrap());
            } else {
                break;
            }
        }
        number
    }
}

/// 语法分析器
/// 
/// 理论映射: parse: [Token] → AST
pub struct Parser {
    pub current_position: usize,
}

impl Parser {
    pub fn new() -> Self {
        Self { current_position: 0 }
    }
    
    /// 语法分析
    /// 
    /// 理论映射: parse(tokens) → AbstractSyntaxTree
    pub fn parse(&mut self, tokens: &[Token]) -> Result<AST, CompilationError> {
        self.current_position = 0;
        let mut functions = Vec::new();
        
        while self.current_position < tokens.len() {
            if let Some(function) = self.parse_function(tokens)? {
                functions.push(function);
            }
        }
        
        Ok(AST { functions })
    }
    
    fn parse_function(&mut self, tokens: &[Token]) -> Result<Option<Function>, CompilationError> {
        if self.current_position >= tokens.len() {
            return Ok(None);
        }
        
        // 简化函数解析
        if tokens[self.current_position].token_type == TokenType::Function {
            self.current_position += 1; // 跳过 'fn'
            
            let name = if self.current_position < tokens.len() {
                tokens[self.current_position].value.clone()
            } else {
                return Err(CompilationError::SyntaxError("Expected function name".to_string()));
            };
            self.current_position += 1;
            
            // 跳过参数和返回类型（简化）
            while self.current_position < tokens.len() && 
                  tokens[self.current_position].token_type != TokenType::Punctuation {
                self.current_position += 1;
            }
            
            let body = self.parse_function_body(tokens)?;
            
            Ok(Some(Function {
                name,
                parameters: Vec::new(), // 简化
                return_type: None, // 简化
                body,
            }))
        } else {
            Ok(None)
        }
    }
    
    fn parse_function_body(&mut self, tokens: &[Token]) -> Result<Vec<Statement>, CompilationError> {
        let mut statements = Vec::new();
        
        // 简化语句解析
        while self.current_position < tokens.len() && 
              tokens[self.current_position].token_type != TokenType::Punctuation {
            statements.push(Statement::Expression(Expression::Literal("0".to_string())));
            self.current_position += 1;
        }
        
        Ok(statements)
    }
}

/// 语义分析器
/// 
/// 理论映射: analyze: AST → SemanticInfo
pub struct SemanticAnalyzer {
    pub symbol_table: HashMap<String, SymbolInfo>,
}

impl SemanticAnalyzer {
    pub fn new() -> Self {
        Self {
            symbol_table: HashMap::new(),
        }
    }
    
    /// 语义分析
    /// 
    /// 理论映射: analyze(ast) → SemanticInfo
    pub fn analyze(&mut self, ast: &AST) -> Result<SemanticInfo, CompilationError> {
        let mut type_info = HashMap::new();
        let mut memory_info = HashMap::new();
        
        for function in &ast.functions {
            // 类型检查
            let function_type = self.analyze_function_type(function)?;
            type_info.insert(function.name.clone(), function_type);
            
            // 内存分析
            let memory_usage = self.analyze_memory_usage(function)?;
            memory_info.insert(function.name.clone(), memory_usage);
        }
        
        Ok(SemanticInfo {
            type_info,
            memory_info,
            symbol_table: self.symbol_table.clone(),
        })
    }
    
    fn analyze_function_type(&self, function: &Function) -> Result<FuncType, CompilationError> {
        // 简化类型分析
        Ok(FuncType {
            params: vec![ValueType::I32], // 简化参数类型
            results: vec![ValueType::I32], // 简化返回类型
        })
    }
    
    fn analyze_memory_usage(&self, function: &Function) -> Result<MemoryUsage, CompilationError> {
        // 简化内存使用分析
        Ok(MemoryUsage {
            stack_size: 1024, // 固定栈大小
            heap_size: 4096,  // 固定堆大小
            local_variables: function.parameters.len() as u32,
        })
    }
}

/// 代码生成器
/// 
/// 理论映射: generate: AST × SemanticInfo → WasmModule
pub struct CodeGenerator {
    pub type_converter: TypeConverter,
    pub instruction_generator: InstructionGenerator,
}

impl CodeGenerator {
    pub fn new() -> Self {
        Self {
            type_converter: TypeConverter::new(),
            instruction_generator: InstructionGenerator::new(),
        }
    }
    
    /// 代码生成
    /// 
    /// 理论映射: generate(ast, semantic_info) → WasmModule
    pub fn generate(&self, ast: &AST, semantic_info: &SemanticInfo) -> Result<WasmModule, CompilationError> {
        let mut types = Vec::new();
        let mut functions = Vec::new();
        let mut memories = Vec::new();
        let mut globals = Vec::new();
        let mut exports = Vec::new();
        
        for function in &ast.functions {
            // 生成函数类型
            let func_type = self.type_converter.convert_function_type(function, semantic_info)?;
            types.push(func_type.clone());
            
            // 生成函数实现
            let wasm_function = self.generate_function(function, semantic_info)?;
            functions.push(wasm_function);
            
            // 生成导出
            exports.push(Export {
                name: function.name.clone(),
                desc: ExportDesc::Func(functions.len() as u32 - 1),
            });
        }
        
        // 生成内存定义
        memories.push(Memory {
            limits: Limits {
                initial: 1,
                maximum: Some(10),
            },
        });
        
        Ok(WasmModule {
            types,
            functions,
            tables: Vec::new(),
            memories,
            globals,
            imports: Vec::new(),
            exports,
            start: None,
            data: Vec::new(),
            elements: Vec::new(),
        })
    }
    
    fn generate_function(&self, function: &Function, semantic_info: &SemanticInfo) -> Result<WasmFunction, CompilationError> {
        let type_index = 0; // 简化类型索引
        let locals = vec![ValueType::I32]; // 简化局部变量
        let body = self.instruction_generator.generate_instructions(&function.body)?;
        
        Ok(WasmFunction {
            type_index,
            locals,
            body,
        })
    }
}

/// 优化器
/// 
/// 理论映射: optimize: WasmModule → WasmModule
pub struct Optimizer {
    pub optimization_passes: Vec<Box<dyn OptimizationPass>>,
}

impl Optimizer {
    pub fn new() -> Self {
        let mut passes: Vec<Box<dyn OptimizationPass>> = Vec::new();
        passes.push(Box::new(DeadCodeElimination));
        passes.push(Box::new(ConstantFolding));
        passes.push(Box::new(FunctionInlining));
        
        Self {
            optimization_passes: passes,
        }
    }
    
    /// 优化WebAssembly模块
    /// 
    /// 理论映射: optimize(module) → OptimizedModule
    pub fn optimize(&self, mut module: WasmModule) -> Result<WasmModule, CompilationError> {
        for pass in &self.optimization_passes {
            module = pass.apply(module)?;
        }
        
        Ok(module)
    }
}

/// 类型转换器
/// 
/// 理论映射: types: RustTypes → WasmTypes
pub struct TypeConverter {
    pub type_mapping: HashMap<String, ValueType>,
}

impl TypeConverter {
    pub fn new() -> Self {
        let mut type_mapping = HashMap::new();
        type_mapping.insert("i32".to_string(), ValueType::I32);
        type_mapping.insert("i64".to_string(), ValueType::I64);
        type_mapping.insert("f32".to_string(), ValueType::F32);
        type_mapping.insert("f64".to_string(), ValueType::F64);
        
        Self { type_mapping }
    }
    
    /// 转换函数类型
    /// 
    /// 理论映射: convert_function_type: RustFunction → WasmFuncType
    pub fn convert_function_type(&self, function: &Function, semantic_info: &SemanticInfo) -> Result<FuncType, CompilationError> {
        // 简化类型转换
        let params = vec![ValueType::I32]; // 默认参数类型
        let results = vec![ValueType::I32]; // 默认返回类型
        
        Ok(FuncType { params, results })
    }
    
    /// 转换值类型
    /// 
    /// 理论映射: convert_value_type: RustType → WasmValueType
    pub fn convert_value_type(&self, rust_type: &str) -> Option<ValueType> {
        self.type_mapping.get(rust_type).cloned()
    }
}

/// 指令生成器
/// 
/// 理论映射: generate_instructions: [Statement] → [Instruction]
pub struct InstructionGenerator {
    pub instruction_mapping: HashMap<String, Instruction>,
}

impl InstructionGenerator {
    pub fn new() -> Self {
        let mut instruction_mapping = HashMap::new();
        instruction_mapping.insert("i32.const".to_string(), Instruction::Const(Value::I32(0)));
        instruction_mapping.insert("i32.add".to_string(), Instruction::Binary(BinaryOp::Add));
        instruction_mapping.insert("i32.sub".to_string(), Instruction::Binary(BinaryOp::Sub));
        instruction_mapping.insert("i32.mul".to_string(), Instruction::Binary(BinaryOp::Mul));
        instruction_mapping.insert("i32.div".to_string(), Instruction::Binary(BinaryOp::Div));
        
        Self { instruction_mapping }
    }
    
    /// 生成指令序列
    /// 
    /// 理论映射: generate_instructions(statements) → [Instruction]
    pub fn generate_instructions(&self, statements: &[Statement]) -> Result<Vec<Instruction>, CompilationError> {
        let mut instructions = Vec::new();
        
        for statement in statements {
            match statement {
                Statement::Expression(expr) => {
                    let expr_instructions = self.generate_expression_instructions(expr)?;
                    instructions.extend(expr_instructions);
                }
                Statement::Return(expr) => {
                    let expr_instructions = self.generate_expression_instructions(expr)?;
                    instructions.extend(expr_instructions);
                    instructions.push(Instruction::Return);
                }
                _ => {
                    // 简化处理其他语句类型
                    instructions.push(Instruction::Const(Value::I32(0)));
                }
            }
        }
        
        Ok(instructions)
    }
    
    fn generate_expression_instructions(&self, expr: &Expression) -> Result<Vec<Instruction>, CompilationError> {
        match expr {
            Expression::Literal(value) => {
                if let Ok(int_value) = value.parse::<i32>() {
                    Ok(vec![Instruction::Const(Value::I32(int_value))])
                } else {
                    Err(CompilationError::CodeGenerationError("Invalid literal".to_string()))
                }
            }
            Expression::Binary(left, op, right) => {
                let mut instructions = Vec::new();
                
                // 生成左操作数指令
                instructions.extend(self.generate_expression_instructions(left)?);
                
                // 生成右操作数指令
                instructions.extend(self.generate_expression_instructions(right)?);
                
                // 生成二元操作指令
                let binary_op = match op.as_str() {
                    "+" => BinaryOp::Add,
                    "-" => BinaryOp::Sub,
                    "*" => BinaryOp::Mul,
                    "/" => BinaryOp::Div,
                    _ => return Err(CompilationError::CodeGenerationError("Unknown operator".to_string())),
                };
                instructions.push(Instruction::Binary(binary_op));
                
                Ok(instructions)
            }
            _ => {
                // 简化处理其他表达式类型
                Ok(vec![Instruction::Const(Value::I32(0))])
            }
        }
    }
}

/// 优化通道
pub trait OptimizationPass {
    fn apply(&self, module: WasmModule) -> Result<WasmModule, CompilationError>;
}

/// 死代码消除
pub struct DeadCodeElimination;

impl OptimizationPass for DeadCodeElimination {
    fn apply(&self, mut module: WasmModule) -> Result<WasmModule, CompilationError> {
        // 简化死代码消除
        module.functions.retain(|f| !f.body.is_empty());
        Ok(module)
    }
}

/// 常量折叠
pub struct ConstantFolding;

impl OptimizationPass for ConstantFolding {
    fn apply(&self, mut module: WasmModule) -> Result<WasmModule, CompilationError> {
        // 简化常量折叠
        for function in &mut module.functions {
            let mut optimized_body = Vec::new();
            let mut i = 0;
            
            while i < function.body.len() {
                if i + 2 < function.body.len() {
                    if let (Instruction::Const(Value::I32(a)), 
                           Instruction::Const(Value::I32(b)), 
                           Instruction::Binary(op)) = 
                        (&function.body[i], &function.body[i + 1], &function.body[i + 2]) {
                        
                        let result = match op {
                            BinaryOp::Add => a + b,
                            BinaryOp::Sub => a - b,
                            BinaryOp::Mul => a * b,
                            BinaryOp::Div => if *b != 0 { a / b } else { 0 },
                        };
                        
                        optimized_body.push(Instruction::Const(Value::I32(result)));
                        i += 3;
                    } else {
                        optimized_body.push(function.body[i].clone());
                        i += 1;
                    }
                } else {
                    optimized_body.push(function.body[i].clone());
                    i += 1;
                }
            }
            
            function.body = optimized_body;
        }
        
        Ok(module)
    }
}

/// 函数内联
pub struct FunctionInlining;

impl OptimizationPass for FunctionInlining {
    fn apply(&self, module: WasmModule) -> Result<WasmModule, CompilationError> {
        // 简化函数内联（实际实现会更复杂）
        Ok(module)
    }
}

// 数据结构定义

#[derive(Debug, Clone)]
pub struct Token {
    pub token_type: TokenType,
    pub value: String,
    pub line: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenType {
    Function,
    Let,
    Mut,
    Return,
    If,
    Else,
    For,
    While,
    Identifier,
    Number,
    Operator,
    Punctuation,
}

#[derive(Debug, Clone)]
pub struct AST {
    pub functions: Vec<Function>,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub parameters: Vec<Parameter>,
    pub return_type: Option<String>,
    pub body: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: String,
    pub type_name: String,
}

#[derive(Debug, Clone)]
pub enum Statement {
    Expression(Expression),
    Return(Expression),
    Let(String, Expression),
    If(Expression, Vec<Statement>, Option<Vec<Statement>>),
}

#[derive(Debug, Clone)]
pub enum Expression {
    Literal(String),
    Identifier(String),
    Binary(Box<Expression>, String, Box<Expression>),
    Call(String, Vec<Expression>),
}

#[derive(Debug, Clone)]
pub struct SemanticInfo {
    pub type_info: HashMap<String, FuncType>,
    pub memory_info: HashMap<String, MemoryUsage>,
    pub symbol_table: HashMap<String, SymbolInfo>,
}

#[derive(Debug, Clone)]
pub struct SymbolInfo {
    pub name: String,
    pub type_name: String,
    pub scope: String,
}

#[derive(Debug, Clone)]
pub struct MemoryUsage {
    pub stack_size: u32,
    pub heap_size: u32,
    pub local_variables: u32,
}

#[derive(Debug, Clone)]
pub struct WasmModule {
    pub types: Vec<FuncType>,
    pub functions: Vec<WasmFunction>,
    pub tables: Vec<Table>,
    pub memories: Vec<Memory>,
    pub globals: Vec<Global>,
    pub imports: Vec<Import>,
    pub exports: Vec<Export>,
    pub start: Option<u32>,
    pub data: Vec<DataSegment>,
    pub elements: Vec<ElementSegment>,
}

#[derive(Debug, Clone)]
pub struct FuncType {
    pub params: Vec<ValueType>,
    pub results: Vec<ValueType>,
}

#[derive(Debug, Clone)]
pub struct WasmFunction {
    pub type_index: u32,
    pub locals: Vec<ValueType>,
    pub body: Vec<Instruction>,
}

#[derive(Debug, Clone)]
pub struct Table {
    pub element_type: RefType,
    pub limits: Limits,
}

#[derive(Debug, Clone)]
pub struct Memory {
    pub limits: Limits,
}

#[derive(Debug, Clone)]
pub struct Global {
    pub value_type: ValueType,
    pub mutable: bool,
    pub init_expr: Vec<Instruction>,
}

#[derive(Debug, Clone)]
pub struct Import {
    pub module: String,
    pub name: String,
    pub desc: ImportDesc,
}

#[derive(Debug, Clone)]
pub enum ImportDesc {
    Func(u32),
    Table(Table),
    Memory(Memory),
    Global(Global),
}

#[derive(Debug, Clone)]
pub struct Export {
    pub name: String,
    pub desc: ExportDesc,
}

#[derive(Debug, Clone)]
pub enum ExportDesc {
    Func(u32),
    Table(u32),
    Memory(u32),
    Global(u32),
}

#[derive(Debug, Clone)]
pub struct DataSegment {
    pub memory_index: u32,
    pub offset: Vec<Instruction>,
    pub data: Vec<u8>,
}

#[derive(Debug, Clone)]
pub struct ElementSegment {
    pub table_index: u32,
    pub offset: Vec<Instruction>,
    pub elements: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ValueType {
    I32,
    I64,
    F32,
    F64,
    V128,
    RefNull,
    Ref(u32),
}

#[derive(Debug, Clone, PartialEq)]
pub enum RefType {
    FuncRef,
    ExternRef,
}

#[derive(Debug, Clone)]
pub struct Limits {
    pub initial: u32,
    pub maximum: Option<u32>,
}

#[derive(Debug, Clone)]
pub enum Instruction {
    Const(Value),
    Binary(BinaryOp),
    LocalGet(u32),
    LocalSet(u32),
    Call(u32),
    Return,
    Drop,
    Select,
    Block(Vec<Instruction>),
    Loop(Vec<Instruction>),
    If(Vec<Instruction>, Vec<Instruction>),
    Br(u32),
    BrIf(u32),
    BrTable(Vec<u32>, u32),
}

#[derive(Debug, Clone)]
pub enum Value {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
}

#[derive(Debug, Clone)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Rotl,
    Rotr,
}

#[derive(Debug)]
pub enum CompilationError {
    LexicalError(String),
    SyntaxError(String),
    SemanticError(String),
    CodeGenerationError(String),
    OptimizationError(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 测试编译流水线
    #[test]
    fn test_compilation_pipeline() {
        let pipeline = CompilationPipeline::new();
        let source_code = r#"
            fn add(a: i32, b: i32) -> i32 {
                return a + b;
            }
        "#;
        
        let result = pipeline.compile(source_code);
        assert!(result.is_ok());
        
        let wasm_module = result.unwrap();
        assert!(!wasm_module.functions.is_empty());
        assert!(!wasm_module.types.is_empty());
    }

    /// 测试词法分析
    #[test]
    fn test_lexer() {
        let lexer = Lexer::new();
        let source = "fn add(a: i32) -> i32 { return a + 1; }";
        
        let tokens = lexer.tokenize(source);
        assert!(tokens.is_ok());
        
        let tokens = tokens.unwrap();
        assert!(!tokens.is_empty());
        assert_eq!(tokens[0].token_type, TokenType::Function);
    }

    /// 测试语法分析
    #[test]
    fn test_parser() {
        let mut parser = Parser::new();
        let tokens = vec![
            Token { token_type: TokenType::Function, value: "fn".to_string(), line: 1 },
            Token { token_type: TokenType::Identifier, value: "add".to_string(), line: 1 },
            Token { token_type: TokenType::Punctuation, value: "(".to_string(), line: 1 },
            Token { token_type: TokenType::Punctuation, value: ")".to_string(), line: 1 },
        ];
        
        let ast = parser.parse(&tokens);
        assert!(ast.is_ok());
    }

    /// 测试语义分析
    #[test]
    fn test_semantic_analyzer() {
        let mut analyzer = SemanticAnalyzer::new();
        let ast = AST {
            functions: vec![
                Function {
                    name: "test".to_string(),
                    parameters: vec![],
                    return_type: None,
                    body: vec![],
                }
            ]
        };
        
        let semantic_info = analyzer.analyze(&ast);
        assert!(semantic_info.is_ok());
    }

    /// 测试代码生成
    #[test]
    fn test_code_generator() {
        let generator = CodeGenerator::new();
        let ast = AST {
            functions: vec![
                Function {
                    name: "test".to_string(),
                    parameters: vec![],
                    return_type: None,
                    body: vec![],
                }
            ]
        };
        let semantic_info = SemanticInfo {
            type_info: HashMap::new(),
            memory_info: HashMap::new(),
            symbol_table: HashMap::new(),
        };
        
        let wasm_module = generator.generate(&ast, &semantic_info);
        assert!(wasm_module.is_ok());
    }

    /// 测试优化器
    #[test]
    fn test_optimizer() {
        let optimizer = Optimizer::new();
        let wasm_module = WasmModule {
            types: vec![],
            functions: vec![],
            tables: vec![],
            memories: vec![],
            globals: vec![],
            imports: vec![],
            exports: vec![],
            start: None,
            data: vec![],
            elements: vec![],
        };
        
        let optimized_module = optimizer.optimize(wasm_module);
        assert!(optimized_module.is_ok());
    }

    /// 测试类型转换
    #[test]
    fn test_type_converter() {
        let converter = TypeConverter::new();
        
        let wasm_type = converter.convert_value_type("i32");
        assert_eq!(wasm_type, Some(ValueType::I32));
        
        let wasm_type = converter.convert_value_type("f64");
        assert_eq!(wasm_type, Some(ValueType::F64));
    }

    /// 测试指令生成
    #[test]
    fn test_instruction_generator() {
        let generator = InstructionGenerator::new();
        let expression = Expression::Literal("42".to_string());
        
        let instructions = generator.generate_expression_instructions(&expression);
        assert!(instructions.is_ok());
        
        let instructions = instructions.unwrap();
        assert_eq!(instructions.len(), 1);
    }
}

/// 示例用法
pub async fn run_examples() {
    println!("=== WebAssembly编译流水线案例 ===");
    
    // 1. 创建编译流水线
    println!("\n1. 创建编译流水线:");
    let pipeline = CompilationPipeline::new();
    println!("   编译流水线创建成功");
    
    // 2. 编译简单函数
    println!("\n2. 编译简单函数:");
    let source_code = r#"
        fn factorial(n: i32) -> i32 {
            if n <= 1 {
                return 1;
            }
            return n * factorial(n - 1);
        }
    "#;
    
    match pipeline.compile(source_code) {
        Ok(wasm_module) => {
            println!("   编译成功");
            println!("   生成函数数量: {}", wasm_module.functions.len());
            println!("   类型定义数量: {}", wasm_module.types.len());
            println!("   导出项数量: {}", wasm_module.exports.len());
        }
        Err(error) => {
            println!("   编译失败: {:?}", error);
        }
    }
    
    // 3. 测试词法分析
    println!("\n3. 词法分析测试:");
    let lexer = Lexer::new();
    let test_source = "fn add(a: i32, b: i32) -> i32 { return a + b; }";
    
    match lexer.tokenize(test_source) {
        Ok(tokens) => {
            println!("   词法分析成功，生成 {} 个标记", tokens.len());
            for (i, token) in tokens.iter().enumerate() {
                println!("   标记 {}: {:?} = '{}'", i, token.token_type, token.value);
            }
        }
        Err(error) => {
            println!("   词法分析失败: {:?}", error);
        }
    }
    
    // 4. 测试语法分析
    println!("\n4. 语法分析测试:");
    let mut parser = Parser::new();
    let tokens = vec![
        Token { token_type: TokenType::Function, value: "fn".to_string(), line: 1 },
        Token { token_type: TokenType::Identifier, value: "test".to_string(), line: 1 },
        Token { token_type: TokenType::Punctuation, value: "(".to_string(), line: 1 },
        Token { token_type: TokenType::Punctuation, value: ")".to_string(), line: 1 },
    ];
    
    match parser.parse(&tokens) {
        Ok(ast) => {
            println!("   语法分析成功");
            println!("   抽象语法树包含 {} 个函数", ast.functions.len());
        }
        Err(error) => {
            println!("   语法分析失败: {:?}", error);
        }
    }
    
    // 5. 测试语义分析
    println!("\n5. 语义分析测试:");
    let mut analyzer = SemanticAnalyzer::new();
    let ast = AST {
        functions: vec![
            Function {
                name: "test_function".to_string(),
                parameters: vec![],
                return_type: None,
                body: vec![],
            }
        ]
    };
    
    match analyzer.analyze(&ast) {
        Ok(semantic_info) => {
            println!("   语义分析成功");
            println!("   类型信息数量: {}", semantic_info.type_info.len());
            println!("   内存信息数量: {}", semantic_info.memory_info.len());
            println!("   符号表大小: {}", semantic_info.symbol_table.len());
        }
        Err(error) => {
            println!("   语义分析失败: {:?}", error);
        }
    }
    
    // 6. 测试代码生成
    println!("\n6. 代码生成测试:");
    let generator = CodeGenerator::new();
    let ast = AST {
        functions: vec![
            Function {
                name: "generated_function".to_string(),
                parameters: vec![],
                return_type: None,
                body: vec![],
            }
        ]
    };
    let semantic_info = SemanticInfo {
        type_info: HashMap::new(),
        memory_info: HashMap::new(),
        symbol_table: HashMap::new(),
    };
    
    match generator.generate(&ast, &semantic_info) {
        Ok(wasm_module) => {
            println!("   代码生成成功");
            println!("   WebAssembly模块包含:");
            println!("     - {} 个类型定义", wasm_module.types.len());
            println!("     - {} 个函数", wasm_module.functions.len());
            println!("     - {} 个内存定义", wasm_module.memories.len());
            println!("     - {} 个导出项", wasm_module.exports.len());
        }
        Err(error) => {
            println!("   代码生成失败: {:?}", error);
        }
    }
    
    // 7. 测试优化器
    println!("\n7. 优化器测试:");
    let optimizer = Optimizer::new();
    let wasm_module = WasmModule {
        types: vec![
            FuncType {
                params: vec![ValueType::I32, ValueType::I32],
                results: vec![ValueType::I32],
            }
        ],
        functions: vec![
            WasmFunction {
                type_index: 0,
                locals: vec![ValueType::I32],
                body: vec![
                    Instruction::Const(Value::I32(5)),
                    Instruction::Const(Value::I32(3)),
                    Instruction::Binary(BinaryOp::Add),
                ],
            }
        ],
        tables: vec![],
        memories: vec![Memory { limits: Limits { initial: 1, maximum: Some(10) } }],
        globals: vec![],
        imports: vec![],
        exports: vec![],
        start: None,
        data: vec![],
        elements: vec![],
    };
    
    match optimizer.optimize(wasm_module) {
        Ok(optimized_module) => {
            println!("   优化成功");
            println!("   优化后模块包含 {} 个函数", optimized_module.functions.len());
        }
        Err(error) => {
            println!("   优化失败: {:?}", error);
        }
    }
    
    // 8. 测试类型转换
    println!("\n8. 类型转换测试:");
    let converter = TypeConverter::new();
    
    let rust_types = vec!["i32", "i64", "f32", "f64"];
    for rust_type in rust_types {
        match converter.convert_value_type(rust_type) {
            Some(wasm_type) => {
                println!("   Rust类型 '{}' 转换为 WebAssembly类型: {:?}", rust_type, wasm_type);
            }
            None => {
                println!("   Rust类型 '{}' 无法转换", rust_type);
            }
        }
    }
    
    // 9. 测试指令生成
    println!("\n9. 指令生成测试:");
    let generator = InstructionGenerator::new();
    
    let expressions = vec![
        Expression::Literal("42".to_string()),
        Expression::Binary(
            Box::new(Expression::Literal("10".to_string())),
            "+".to_string(),
            Box::new(Expression::Literal("32".to_string()))
        ),
    ];
    
    for (i, expr) in expressions.iter().enumerate() {
        match generator.generate_expression_instructions(expr) {
            Ok(instructions) => {
                println!("   表达式 {} 生成 {} 条指令", i, instructions.len());
                for (j, instruction) in instructions.iter().enumerate() {
                    println!("     指令 {}: {:?}", j, instruction);
                }
            }
            Err(error) => {
                println!("   表达式 {} 指令生成失败: {:?}", i, error);
            }
        }
    }
    
    // 10. 验证编译正确性
    println!("\n10. 编译正确性验证:");
    let test_program = "fn add(a: i32, b: i32) -> i32 { return a + b; }";
    let test_module = WasmModule {
        types: vec![
            FuncType {
                params: vec![ValueType::I32, ValueType::I32],
                results: vec![ValueType::I32],
            }
        ],
        functions: vec![
            WasmFunction {
                type_index: 0,
                locals: vec![ValueType::I32, ValueType::I32],
                body: vec![
                    Instruction::LocalGet(0),
                    Instruction::LocalGet(1),
                    Instruction::Binary(BinaryOp::Add),
                ],
            }
        ],
        tables: vec![],
        memories: vec![Memory { limits: Limits { initial: 1, maximum: Some(10) } }],
        globals: vec![],
        imports: vec![],
        exports: vec![],
        start: None,
        data: vec![],
        elements: vec![],
    };
    
    let is_correct = pipeline.verify_correctness(test_program, &test_module);
    println!("   编译正确性验证: {}", if is_correct { "通过" } else { "失败" });
} 