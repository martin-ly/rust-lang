# Rust编译器架构实现理论 V32

**创建日期**: 2025-01-27  
**版本**: V32  
**目的**: 建立Rust编译器架构的完整实现理论  
**状态**: 活跃维护

## 编译器架构概览

### Rust编译器的特点

Rust编译器具有以下核心特征：

1. **多阶段编译**: 从源码到机器码的完整流程
2. **类型检查**: 编译时类型安全保证
3. **借用检查**: 内存安全静态分析
4. **优化**: 多级代码优化
5. **错误处理**: 友好的错误信息

## 编译器阶段

### 1. 词法分析 (Lexical Analysis)

#### 1.1 词法分析器实现

```rust
// 词法分析器
struct Lexer {
    input: Vec<char>,
    position: usize,
    current_char: Option<char>,
}

#[derive(Debug, Clone, PartialEq)]
enum Token {
    // 关键字
    Fn, Let, Mut, If, Else, Loop, While, For, In, Return, Break, Continue,
    // 标识符
    Identifier(String),
    // 字面量
    Integer(i64),
    Float(f64),
    String(String),
    Char(char),
    Boolean(bool),
    // 操作符
    Plus, Minus, Star, Slash, Percent,
    Equal, EqualEqual, Bang, BangEqual,
    Less, LessEqual, Greater, GreaterEqual,
    // 分隔符
    LeftParen, RightParen, LeftBrace, RightBrace,
    LeftBracket, RightBracket, Semicolon, Comma,
    Dot, Arrow, Colon, DoubleColon,
    // 特殊
    Eof,
}

impl Lexer {
    fn new(input: &str) -> Self {
        let chars: Vec<char> = input.chars().collect();
        let current_char = chars.first().copied();
        
        Lexer {
            input: chars,
            position: 0,
            current_char,
        }
    }
    
    fn advance(&mut self) {
        self.position += 1;
        self.current_char = self.input.get(self.position).copied();
    }
    
    fn peek(&self) -> Option<char> {
        self.input.get(self.position + 1).copied()
    }
    
    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.current_char {
            if ch.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }
    
    fn read_identifier(&mut self) -> String {
        let mut identifier = String::new();
        
        while let Some(ch) = self.current_char {
            if ch.is_alphanumeric() || ch == '_' {
                identifier.push(ch);
                self.advance();
            } else {
                break;
            }
        }
        
        identifier
    }
    
    fn read_number(&mut self) -> Token {
        let mut number = String::new();
        let mut is_float = false;
        
        while let Some(ch) = self.current_char {
            if ch.is_digit(10) {
                number.push(ch);
                self.advance();
            } else if ch == '.' && !is_float {
                number.push(ch);
                is_float = true;
                self.advance();
            } else {
                break;
            }
        }
        
        if is_float {
            Token::Float(number.parse().unwrap())
        } else {
            Token::Integer(number.parse().unwrap())
        }
    }
    
    fn read_string(&mut self) -> Token {
        let mut string = String::new();
        self.advance(); // 跳过开始的引号
        
        while let Some(ch) = self.current_char {
            if ch == '"' {
                self.advance();
                break;
            } else if ch == '\\' {
                self.advance();
                if let Some(escaped) = self.current_char {
                    string.push(match escaped {
                        'n' => '\n',
                        't' => '\t',
                        'r' => '\r',
                        '\\' => '\\',
                        '"' => '"',
                        _ => escaped,
                    });
                    self.advance();
                }
            } else {
                string.push(ch);
                self.advance();
            }
        }
        
        Token::String(string)
    }
    
    fn next_token(&mut self) -> Token {
        self.skip_whitespace();
        
        match self.current_char {
            None => Token::Eof,
            Some(ch) => {
                match ch {
                    'a'..='z' | 'A'..='Z' | '_' => {
                        let identifier = self.read_identifier();
                        match identifier.as_str() {
                            "fn" => Token::Fn,
                            "let" => Token::Let,
                            "mut" => Token::Mut,
                            "if" => Token::If,
                            "else" => Token::Else,
                            "loop" => Token::Loop,
                            "while" => Token::While,
                            "for" => Token::For,
                            "in" => Token::In,
                            "return" => Token::Return,
                            "break" => Token::Break,
                            "continue" => Token::Continue,
                            "true" => Token::Boolean(true),
                            "false" => Token::Boolean(false),
                            _ => Token::Identifier(identifier),
                        }
                    }
                    '0'..='9' => self.read_number(),
                    '"' => self.read_string(),
                    '+' => {
                        self.advance();
                        Token::Plus
                    }
                    '-' => {
                        self.advance();
                        if self.peek() == Some('>') {
                            self.advance();
                            Token::Arrow
                        } else {
                            Token::Minus
                        }
                    }
                    '*' => {
                        self.advance();
                        Token::Star
                    }
                    '/' => {
                        self.advance();
                        Token::Slash
                    }
                    '%' => {
                        self.advance();
                        Token::Percent
                    }
                    '=' => {
                        self.advance();
                        if self.current_char == Some('=') {
                            self.advance();
                            Token::EqualEqual
                        } else {
                            Token::Equal
                        }
                    }
                    '!' => {
                        self.advance();
                        if self.current_char == Some('=') {
                            self.advance();
                            Token::BangEqual
                        } else {
                            Token::Bang
                        }
                    }
                    '<' => {
                        self.advance();
                        if self.current_char == Some('=') {
                            self.advance();
                            Token::LessEqual
                        } else {
                            Token::Less
                        }
                    }
                    '>' => {
                        self.advance();
                        if self.current_char == Some('=') {
                            self.advance();
                            Token::GreaterEqual
                        } else {
                            Token::Greater
                        }
                    }
                    '(' => {
                        self.advance();
                        Token::LeftParen
                    }
                    ')' => {
                        self.advance();
                        Token::RightParen
                    }
                    '{' => {
                        self.advance();
                        Token::LeftBrace
                    }
                    '}' => {
                        self.advance();
                        Token::RightBrace
                    }
                    '[' => {
                        self.advance();
                        Token::LeftBracket
                    }
                    ']' => {
                        self.advance();
                        Token::RightBracket
                    }
                    ';' => {
                        self.advance();
                        Token::Semicolon
                    }
                    ',' => {
                        self.advance();
                        Token::Comma
                    }
                    '.' => {
                        self.advance();
                        Token::Dot
                    }
                    ':' => {
                        self.advance();
                        if self.current_char == Some(':') {
                            self.advance();
                            Token::DoubleColon
                        } else {
                            Token::Colon
                        }
                    }
                    _ => {
                        self.advance();
                        Token::Eof // 错误处理简化
                    }
                }
            }
        }
    }
}
```

### 2. 语法分析 (Syntax Analysis)

#### 2.1 抽象语法树 (AST)

```rust
// 抽象语法树节点
#[derive(Debug, Clone)]
enum AstNode {
    // 表达式
    BinaryExpr {
        left: Box<AstNode>,
        operator: BinaryOperator,
        right: Box<AstNode>,
    },
    UnaryExpr {
        operator: UnaryOperator,
        operand: Box<AstNode>,
    },
    LiteralExpr {
        value: LiteralValue,
    },
    VariableExpr {
        name: String,
    },
    CallExpr {
        function: Box<AstNode>,
        arguments: Vec<AstNode>,
    },
    BlockExpr {
        statements: Vec<AstNode>,
    },
    IfExpr {
        condition: Box<AstNode>,
        then_branch: Box<AstNode>,
        else_branch: Option<Box<AstNode>>,
    },
    LoopExpr {
        body: Box<AstNode>,
    },
    WhileExpr {
        condition: Box<AstNode>,
        body: Box<AstNode>,
    },
    ForExpr {
        variable: String,
        iterator: Box<AstNode>,
        body: Box<AstNode>,
    },
    
    // 语句
    LetStmt {
        name: String,
        mutable: bool,
        type_annotation: Option<TypeAnnotation>,
        initializer: Option<Box<AstNode>>,
    },
    ReturnStmt {
        value: Option<Box<AstNode>>,
    },
    ExprStmt {
        expression: Box<AstNode>,
    },
    
    // 声明
    FunctionDecl {
        name: String,
        parameters: Vec<Parameter>,
        return_type: Option<TypeAnnotation>,
        body: Box<AstNode>,
    },
    StructDecl {
        name: String,
        fields: Vec<StructField>,
    },
    EnumDecl {
        name: String,
        variants: Vec<EnumVariant>,
    },
    TraitDecl {
        name: String,
        methods: Vec<MethodDecl>,
    },
    ImplDecl {
        trait_name: Option<String>,
        type_name: String,
        methods: Vec<MethodDecl>,
    },
}

#[derive(Debug, Clone)]
enum BinaryOperator {
    Add, Sub, Mul, Div, Mod,
    Equal, NotEqual, Less, LessEqual, Greater, GreaterEqual,
    And, Or,
}

#[derive(Debug, Clone)]
enum UnaryOperator {
    Neg, Not,
}

#[derive(Debug, Clone)]
enum LiteralValue {
    Integer(i64),
    Float(f64),
    String(String),
    Char(char),
    Boolean(bool),
}

#[derive(Debug, Clone)]
struct TypeAnnotation {
    name: String,
    generic_args: Vec<TypeAnnotation>,
}

#[derive(Debug, Clone)]
struct Parameter {
    name: String,
    type_annotation: TypeAnnotation,
}

#[derive(Debug, Clone)]
struct StructField {
    name: String,
    type_annotation: TypeAnnotation,
}

#[derive(Debug, Clone)]
struct EnumVariant {
    name: String,
    fields: Vec<StructField>,
}

#[derive(Debug, Clone)]
struct MethodDecl {
    name: String,
    parameters: Vec<Parameter>,
    return_type: Option<TypeAnnotation>,
    body: Option<Box<AstNode>>,
}
```

#### 2.2 递归下降解析器

```rust
// 递归下降解析器
struct Parser {
    tokens: Vec<Token>,
    current: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Parser {
            tokens,
            current: 0,
        }
    }
    
    fn current_token(&self) -> Option<&Token> {
        self.tokens.get(self.current)
    }
    
    fn advance(&mut self) -> Option<&Token> {
        if self.current < self.tokens.len() {
            self.current += 1;
        }
        self.current_token()
    }
    
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.current + 1)
    }
    
    fn check(&self, token_type: &Token) -> bool {
        if let Some(current) = self.current_token() {
            std::mem::discriminant(current) == std::mem::discriminant(token_type)
        } else {
            false
        }
    }
    
    fn match_token(&mut self, token_type: &Token) -> bool {
        if self.check(token_type) {
            self.advance();
            true
        } else {
            false
        }
    }
    
    fn parse(&mut self) -> Result<Vec<AstNode>, String> {
        let mut declarations = Vec::new();
        
        while self.current < self.tokens.len() {
            let declaration = self.parse_declaration()?;
            declarations.push(declaration);
        }
        
        Ok(declarations)
    }
    
    fn parse_declaration(&mut self) -> Result<AstNode, String> {
        match self.current_token() {
            Some(Token::Fn) => self.parse_function_declaration(),
            Some(Token::Struct) => self.parse_struct_declaration(),
            Some(Token::Enum) => self.parse_enum_declaration(),
            Some(Token::Trait) => self.parse_trait_declaration(),
            Some(Token::Impl) => self.parse_impl_declaration(),
            _ => self.parse_statement(),
        }
    }
    
    fn parse_function_declaration(&mut self) -> Result<AstNode, String> {
        self.advance(); // 跳过 'fn'
        
        let name = if let Some(Token::Identifier(name)) = self.current_token() {
            name.clone()
        } else {
            return Err("Expected function name".to_string());
        };
        self.advance();
        
        if !self.match_token(&Token::LeftParen) {
            return Err("Expected '(' after function name".to_string());
        }
        
        let mut parameters = Vec::new();
        while !self.check(&Token::RightParen) {
            let param = self.parse_parameter()?;
            parameters.push(param);
            
            if !self.match_token(&Token::Comma) {
                break;
            }
        }
        
        if !self.match_token(&Token::RightParen) {
            return Err("Expected ')' after parameters".to_string());
        }
        
        let return_type = if self.match_token(&Token::Arrow) {
            Some(self.parse_type_annotation()?)
        } else {
            None
        };
        
        let body = self.parse_block_expression()?;
        
        Ok(AstNode::FunctionDecl {
            name,
            parameters,
            return_type,
            body: Box::new(body),
        })
    }
    
    fn parse_parameter(&mut self) -> Result<Parameter, String> {
        let name = if let Some(Token::Identifier(name)) = self.current_token() {
            name.clone()
        } else {
            return Err("Expected parameter name".to_string());
        };
        self.advance();
        
        if !self.match_token(&Token::Colon) {
            return Err("Expected ':' after parameter name".to_string());
        }
        
        let type_annotation = self.parse_type_annotation()?;
        
        Ok(Parameter {
            name,
            type_annotation,
        })
    }
    
    fn parse_type_annotation(&mut self) -> Result<TypeAnnotation, String> {
        let name = if let Some(Token::Identifier(name)) = self.current_token() {
            name.clone()
        } else {
            return Err("Expected type name".to_string());
        };
        self.advance();
        
        let generic_args = if self.match_token(&Token::Less) {
            let mut args = Vec::new();
            while !self.check(&Token::Greater) {
                let arg = self.parse_type_annotation()?;
                args.push(arg);
                
                if !self.match_token(&Token::Comma) {
                    break;
                }
            }
            
            if !self.match_token(&Token::Greater) {
                return Err("Expected '>' after generic arguments".to_string());
            }
            
            args
        } else {
            Vec::new()
        };
        
        Ok(TypeAnnotation {
            name,
            generic_args,
        })
    }
    
    fn parse_block_expression(&mut self) -> Result<AstNode, String> {
        if !self.match_token(&Token::LeftBrace) {
            return Err("Expected '{' at start of block".to_string());
        }
        
        let mut statements = Vec::new();
        while !self.check(&Token::RightBrace) {
            let statement = self.parse_statement()?;
            statements.push(statement);
        }
        
        if !self.match_token(&Token::RightBrace) {
            return Err("Expected '}' at end of block".to_string());
        }
        
        Ok(AstNode::BlockExpr { statements })
    }
    
    fn parse_statement(&mut self) -> Result<AstNode, String> {
        match self.current_token() {
            Some(Token::Let) => self.parse_let_statement(),
            Some(Token::Return) => self.parse_return_statement(),
            _ => {
                let expr = self.parse_expression()?;
                if self.match_token(&Token::Semicolon) {
                    Ok(AstNode::ExprStmt {
                        expression: Box::new(expr),
                    })
                } else {
                    Ok(expr)
                }
            }
        }
    }
    
    fn parse_let_statement(&mut self) -> Result<AstNode, String> {
        self.advance(); // 跳过 'let'
        
        let name = if let Some(Token::Identifier(name)) = self.current_token() {
            name.clone()
        } else {
            return Err("Expected variable name".to_string());
        };
        self.advance();
        
        let mutable = self.match_token(&Token::Mut);
        
        let type_annotation = if self.match_token(&Token::Colon) {
            Some(self.parse_type_annotation()?)
        } else {
            None
        };
        
        let initializer = if self.match_token(&Token::Equal) {
            Some(Box::new(self.parse_expression()?))
        } else {
            None
        };
        
        if !self.match_token(&Token::Semicolon) {
            return Err("Expected ';' after let statement".to_string());
        }
        
        Ok(AstNode::LetStmt {
            name,
            mutable,
            type_annotation,
            initializer,
        })
    }
    
    fn parse_return_statement(&mut self) -> Result<AstNode, String> {
        self.advance(); // 跳过 'return'
        
        let value = if !self.check(&Token::Semicolon) {
            Some(Box::new(self.parse_expression()?))
        } else {
            None
        };
        
        if !self.match_token(&Token::Semicolon) {
            return Err("Expected ';' after return statement".to_string());
        }
        
        Ok(AstNode::ReturnStmt { value })
    }
    
    fn parse_expression(&mut self) -> Result<AstNode, String> {
        self.parse_assignment()
    }
    
    fn parse_assignment(&mut self) -> Result<AstNode, String> {
        let expr = self.parse_or()?;
        
        if self.match_token(&Token::Equal) {
            let value = self.parse_assignment()?;
            return Ok(AstNode::BinaryExpr {
                left: Box::new(expr),
                operator: BinaryOperator::Equal,
                right: Box::new(value),
            });
        }
        
        Ok(expr)
    }
    
    fn parse_or(&mut self) -> Result<AstNode, String> {
        let mut expr = self.parse_and()?;
        
        while self.match_token(&Token::Or) {
            let right = self.parse_and()?;
            expr = AstNode::BinaryExpr {
                left: Box::new(expr),
                operator: BinaryOperator::Or,
                right: Box::new(right),
            };
        }
        
        Ok(expr)
    }
    
    fn parse_and(&mut self) -> Result<AstNode, String> {
        let mut expr = self.parse_equality()?;
        
        while self.match_token(&Token::And) {
            let right = self.parse_equality()?;
            expr = AstNode::BinaryExpr {
                left: Box::new(expr),
                operator: BinaryOperator::And,
                right: Box::new(right),
            };
        }
        
        Ok(expr)
    }
    
    fn parse_equality(&mut self) -> Result<AstNode, String> {
        let mut expr = self.parse_comparison()?;
        
        while let Some(token) = self.current_token() {
            let operator = match token {
                Token::EqualEqual => BinaryOperator::Equal,
                Token::BangEqual => BinaryOperator::NotEqual,
                _ => break,
            };
            self.advance();
            
            let right = self.parse_comparison()?;
            expr = AstNode::BinaryExpr {
                left: Box::new(expr),
                operator,
                right: Box::new(right),
            };
        }
        
        Ok(expr)
    }
    
    fn parse_comparison(&mut self) -> Result<AstNode, String> {
        let mut expr = self.parse_term()?;
        
        while let Some(token) = self.current_token() {
            let operator = match token {
                Token::Less => BinaryOperator::Less,
                Token::LessEqual => BinaryOperator::LessEqual,
                Token::Greater => BinaryOperator::Greater,
                Token::GreaterEqual => BinaryOperator::GreaterEqual,
                _ => break,
            };
            self.advance();
            
            let right = self.parse_term()?;
            expr = AstNode::BinaryExpr {
                left: Box::new(expr),
                operator,
                right: Box::new(right),
            };
        }
        
        Ok(expr)
    }
    
    fn parse_term(&mut self) -> Result<AstNode, String> {
        let mut expr = self.parse_factor()?;
        
        while let Some(token) = self.current_token() {
            let operator = match token {
                Token::Plus => BinaryOperator::Add,
                Token::Minus => BinaryOperator::Sub,
                _ => break,
            };
            self.advance();
            
            let right = self.parse_factor()?;
            expr = AstNode::BinaryExpr {
                left: Box::new(expr),
                operator,
                right: Box::new(right),
            };
        }
        
        Ok(expr)
    }
    
    fn parse_factor(&mut self) -> Result<AstNode, String> {
        let mut expr = self.parse_unary()?;
        
        while let Some(token) = self.current_token() {
            let operator = match token {
                Token::Star => BinaryOperator::Mul,
                Token::Slash => BinaryOperator::Div,
                Token::Percent => BinaryOperator::Mod,
                _ => break,
            };
            self.advance();
            
            let right = self.parse_unary()?;
            expr = AstNode::BinaryExpr {
                left: Box::new(expr),
                operator,
                right: Box::new(right),
            };
        }
        
        Ok(expr)
    }
    
    fn parse_unary(&mut self) -> Result<AstNode, String> {
        if let Some(token) = self.current_token() {
            let operator = match token {
                Token::Minus => UnaryOperator::Neg,
                Token::Bang => UnaryOperator::Not,
                _ => return self.parse_primary(),
            };
            self.advance();
            
            let operand = self.parse_unary()?;
            return Ok(AstNode::UnaryExpr {
                operator,
                operand: Box::new(operand),
            });
        }
        
        self.parse_primary()
    }
    
    fn parse_primary(&mut self) -> Result<AstNode, String> {
        match self.current_token() {
            Some(Token::Integer(value)) => {
                self.advance();
                Ok(AstNode::LiteralExpr {
                    value: LiteralValue::Integer(*value),
                })
            }
            Some(Token::Float(value)) => {
                self.advance();
                Ok(AstNode::LiteralExpr {
                    value: LiteralValue::Float(*value),
                })
            }
            Some(Token::String(value)) => {
                self.advance();
                Ok(AstNode::LiteralExpr {
                    value: LiteralValue::String(value.clone()),
                })
            }
            Some(Token::Char(value)) => {
                self.advance();
                Ok(AstNode::LiteralExpr {
                    value: LiteralValue::Char(*value),
                })
            }
            Some(Token::Boolean(value)) => {
                self.advance();
                Ok(AstNode::LiteralExpr {
                    value: LiteralValue::Boolean(*value),
                })
            }
            Some(Token::Identifier(name)) => {
                self.advance();
                Ok(AstNode::VariableExpr {
                    name: name.clone(),
                })
            }
            Some(Token::LeftParen) => {
                self.advance();
                let expr = self.parse_expression()?;
                
                if !self.match_token(&Token::RightParen) {
                    return Err("Expected ')' after expression".to_string());
                }
                
                Ok(expr)
            }
            _ => Err("Unexpected token".to_string()),
        }
    }
}
```

### 3. 语义分析 (Semantic Analysis)

#### 3.1 类型检查器

```rust
// 类型检查器
struct TypeChecker {
    environment: TypeEnvironment,
    errors: Vec<String>,
}

impl TypeChecker {
    fn new() -> Self {
        TypeChecker {
            environment: TypeEnvironment::new(),
            errors: Vec::new(),
        }
    }
    
    fn check_program(&mut self, program: &[AstNode]) -> Result<(), Vec<String>> {
        for node in program {
            self.check_declaration(node)?;
        }
        
        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(self.errors.clone())
        }
    }
    
    fn check_declaration(&mut self, node: &AstNode) -> Result<Type, String> {
        match node {
            AstNode::FunctionDecl { name, parameters, return_type, body } => {
                self.check_function_declaration(name, parameters, return_type, body)
            }
            AstNode::LetStmt { name, mutable, type_annotation, initializer } => {
                self.check_let_statement(name, *mutable, type_annotation, initializer)
            }
            _ => self.check_expression(node),
        }
    }
    
    fn check_function_declaration(
        &mut self,
        name: &str,
        parameters: &[Parameter],
        return_type: &Option<TypeAnnotation>,
        body: &AstNode,
    ) -> Result<Type, String> {
        // 创建函数作用域
        let mut function_env = self.environment.clone();
        
        // 添加参数到环境
        let mut param_types = Vec::new();
        for param in parameters {
            let param_type = self.resolve_type_annotation(&param.type_annotation)?;
            function_env.extend(param.name.clone(), param_type.clone());
            param_types.push(param_type);
        }
        
        // 检查返回类型
        let expected_return_type = if let Some(return_type_ann) = return_type {
            self.resolve_type_annotation(return_type_ann)?
        } else {
            Type::Unit
        };
        
        // 检查函数体
        let old_env = std::mem::replace(&mut self.environment, function_env);
        let actual_return_type = self.check_expression(body)?;
        self.environment = old_env;
        
        // 验证返回类型
        if !self.types_compatible(&actual_return_type, &expected_return_type) {
            self.errors.push(format!(
                "Function '{}' returns {:?} but expected {:?}",
                name, actual_return_type, expected_return_type
            ));
        }
        
        Ok(Type::Function(param_types, Box::new(expected_return_type)))
    }
    
    fn check_let_statement(
        &mut self,
        name: &str,
        mutable: bool,
        type_annotation: &Option<TypeAnnotation>,
        initializer: &Option<Box<AstNode>>,
    ) -> Result<Type, String> {
        let variable_type = if let Some(init) = initializer {
            let init_type = self.check_expression(init)?;
            
            if let Some(annotation) = type_annotation {
                let expected_type = self.resolve_type_annotation(annotation)?;
                if !self.types_compatible(&init_type, &expected_type) {
                    self.errors.push(format!(
                        "Cannot assign {:?} to variable '{}' of type {:?}",
                        init_type, name, expected_type
                    ));
                }
                expected_type
            } else {
                init_type
            }
        } else if let Some(annotation) = type_annotation {
            self.resolve_type_annotation(annotation)?
        } else {
            return Err(format!("Variable '{}' must have a type annotation or initializer", name));
        };
        
        self.environment.extend(name.to_string(), variable_type.clone());
        Ok(variable_type)
    }
    
    fn check_expression(&mut self, node: &AstNode) -> Result<Type, String> {
        match node {
            AstNode::BinaryExpr { left, operator, right } => {
                self.check_binary_expression(left, operator, right)
            }
            AstNode::UnaryExpr { operator, operand } => {
                self.check_unary_expression(operator, operand)
            }
            AstNode::LiteralExpr { value } => {
                self.check_literal_expression(value)
            }
            AstNode::VariableExpr { name } => {
                self.check_variable_expression(name)
            }
            AstNode::CallExpr { function, arguments } => {
                self.check_call_expression(function, arguments)
            }
            AstNode::BlockExpr { statements } => {
                self.check_block_expression(statements)
            }
            AstNode::IfExpr { condition, then_branch, else_branch } => {
                self.check_if_expression(condition, then_branch, else_branch)
            }
            _ => Err("Unsupported expression type".to_string()),
        }
    }
    
    fn check_binary_expression(
        &mut self,
        left: &AstNode,
        operator: &BinaryOperator,
        right: &AstNode,
    ) -> Result<Type, String> {
        let left_type = self.check_expression(left)?;
        let right_type = self.check_expression(right)?;
        
        match operator {
            BinaryOperator::Add | BinaryOperator::Sub | BinaryOperator::Mul | BinaryOperator::Div | BinaryOperator::Mod => {
                if self.types_compatible(&left_type, &Type::Int(32)) && self.types_compatible(&right_type, &Type::Int(32)) {
                    Ok(Type::Int(32))
                } else if self.types_compatible(&left_type, &Type::Float(64)) && self.types_compatible(&right_type, &Type::Float(64)) {
                    Ok(Type::Float(64))
                } else {
                    self.errors.push(format!(
                        "Cannot apply {:?} to {:?} and {:?}",
                        operator, left_type, right_type
                    ));
                    Err("Type error".to_string())
                }
            }
            BinaryOperator::Equal | BinaryOperator::NotEqual => {
                if self.types_compatible(&left_type, &right_type) {
                    Ok(Type::Bool)
                } else {
                    self.errors.push(format!(
                        "Cannot compare {:?} and {:?}",
                        left_type, right_type
                    ));
                    Err("Type error".to_string())
                }
            }
            BinaryOperator::Less | BinaryOperator::LessEqual | BinaryOperator::Greater | BinaryOperator::GreaterEqual => {
                if self.types_compatible(&left_type, &Type::Int(32)) && self.types_compatible(&right_type, &Type::Int(32)) {
                    Ok(Type::Bool)
                } else {
                    self.errors.push(format!(
                        "Cannot compare {:?} and {:?}",
                        left_type, right_type
                    ));
                    Err("Type error".to_string())
                }
            }
            BinaryOperator::And | BinaryOperator::Or => {
                if self.types_compatible(&left_type, &Type::Bool) && self.types_compatible(&right_type, &Type::Bool) {
                    Ok(Type::Bool)
                } else {
                    self.errors.push(format!(
                        "Cannot apply {:?} to {:?} and {:?}",
                        operator, left_type, right_type
                    ));
                    Err("Type error".to_string())
                }
            }
        }
    }
    
    fn check_unary_expression(
        &mut self,
        operator: &UnaryOperator,
        operand: &AstNode,
    ) -> Result<Type, String> {
        let operand_type = self.check_expression(operand)?;
        
        match operator {
            UnaryOperator::Neg => {
                if self.types_compatible(&operand_type, &Type::Int(32)) {
                    Ok(Type::Int(32))
                } else if self.types_compatible(&operand_type, &Type::Float(64)) {
                    Ok(Type::Float(64))
                } else {
                    self.errors.push(format!(
                        "Cannot negate {:?}",
                        operand_type
                    ));
                    Err("Type error".to_string())
                }
            }
            UnaryOperator::Not => {
                if self.types_compatible(&operand_type, &Type::Bool) {
                    Ok(Type::Bool)
                } else {
                    self.errors.push(format!(
                        "Cannot apply ! to {:?}",
                        operand_type
                    ));
                    Err("Type error".to_string())
                }
            }
        }
    }
    
    fn check_literal_expression(&self, value: &LiteralValue) -> Result<Type, String> {
        match value {
            LiteralValue::Integer(_) => Ok(Type::Int(32)),
            LiteralValue::Float(_) => Ok(Type::Float(64)),
            LiteralValue::String(_) => Ok(Type::String),
            LiteralValue::Char(_) => Ok(Type::Char),
            LiteralValue::Boolean(_) => Ok(Type::Bool),
        }
    }
    
    fn check_variable_expression(&self, name: &str) -> Result<Type, String> {
        self.environment
            .lookup(name)
            .cloned()
            .ok_or_else(|| format!("Undefined variable '{}'", name))
    }
    
    fn check_call_expression(
        &mut self,
        function: &AstNode,
        arguments: &[AstNode],
    ) -> Result<Type, String> {
        let function_type = self.check_expression(function)?;
        
        match function_type {
            Type::Function(param_types, return_type) => {
                if arguments.len() != param_types.len() {
                    self.errors.push(format!(
                        "Expected {} arguments, got {}",
                        param_types.len(),
                        arguments.len()
                    ));
                    return Err("Argument count mismatch".to_string());
                }
                
                for (arg, expected_type) in arguments.iter().zip(param_types.iter()) {
                    let arg_type = self.check_expression(arg)?;
                    if !self.types_compatible(&arg_type, expected_type) {
                        self.errors.push(format!(
                            "Expected {:?}, got {:?}",
                            expected_type, arg_type
                        ));
                    }
                }
                
                Ok(*return_type)
            }
            _ => {
                self.errors.push(format!(
                    "Cannot call {:?} as a function",
                    function_type
                ));
                Err("Type error".to_string())
            }
        }
    }
    
    fn check_block_expression(&mut self, statements: &[AstNode]) -> Result<Type, String> {
        let mut block_env = self.environment.clone();
        let old_env = std::mem::replace(&mut self.environment, block_env);
        
        let mut last_type = Type::Unit;
        for statement in statements {
            last_type = self.check_expression(statement)?;
        }
        
        self.environment = old_env;
        Ok(last_type)
    }
    
    fn check_if_expression(
        &mut self,
        condition: &AstNode,
        then_branch: &AstNode,
        else_branch: &Option<Box<AstNode>>,
    ) -> Result<Type, String> {
        let condition_type = self.check_expression(condition)?;
        if !self.types_compatible(&condition_type, &Type::Bool) {
            self.errors.push("If condition must be boolean".to_string());
            return Err("Type error".to_string());
        }
        
        let then_type = self.check_expression(then_branch)?;
        
        if let Some(else_branch) = else_branch {
            let else_type = self.check_expression(else_branch)?;
            if !self.types_compatible(&then_type, &else_type) {
                self.errors.push("If branches must have compatible types".to_string());
                return Err("Type error".to_string());
            }
            Ok(then_type)
        } else {
            Ok(then_type)
        }
    }
    
    fn resolve_type_annotation(&self, annotation: &TypeAnnotation) -> Result<Type, String> {
        match annotation.name.as_str() {
            "i32" => Ok(Type::Int(32)),
            "i64" => Ok(Type::Int(64)),
            "f32" => Ok(Type::Float(32)),
            "f64" => Ok(Type::Float(64)),
            "bool" => Ok(Type::Bool),
            "char" => Ok(Type::Char),
            "str" => Ok(Type::String),
            "()" => Ok(Type::Unit),
            _ => {
                // 处理用户定义类型
                Ok(Type::Generic(annotation.name.clone(), annotation.generic_args.iter().map(|arg| {
                    self.resolve_type_annotation(arg).unwrap_or(Type::Unit)
                }).collect()))
            }
        }
    }
    
    fn types_compatible(&self, t1: &Type, t2: &Type) -> bool {
        match (t1, t2) {
            (Type::Int(_), Type::Int(_)) => true,
            (Type::Float(_), Type::Float(_)) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::Char, Type::Char) => true,
            (Type::String, Type::String) => true,
            (Type::Unit, Type::Unit) => true,
            (Type::Function(params1, ret1), Type::Function(params2, ret2)) => {
                if params1.len() != params2.len() {
                    return false;
                }
                for (p1, p2) in params1.iter().zip(params2.iter()) {
                    if !self.types_compatible(p1, p2) {
                        return false;
                    }
                }
                self.types_compatible(ret1, ret2)
            }
            _ => false,
        }
    }
}
```

## 总结

Rust编译器架构实现理论提供了：

1. **词法分析**: 将源码转换为token流
2. **语法分析**: 构建抽象语法树
3. **语义分析**: 类型检查和语义验证
4. **错误处理**: 友好的错误信息
5. **模块化设计**: 清晰的阶段分离

这些理论为Rust编译器的实现提供了坚实的基础。

---

**文档维护**: 本编译器架构实现理论文档将随着Rust形式化理论的发展持续更新和完善。
