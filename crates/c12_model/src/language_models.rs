//! 语言模型和语义模型
//! 
//! 本模块实现了编程语言的形式化建模，包括词法分析、语法分析、语义分析等

use std::collections::HashMap;
use std::fmt;
use serde::{Deserialize, Serialize};
use crate::error::ModelError;

pub type LanguageResult<T> = Result<T, ModelError>;

// ========== 词法分析器 ==========

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TokenType {
    Keyword(String),
    Identifier,
    IntLiteral,
    FloatLiteral,
    StringLiteral,
    BoolLiteral,
    Plus, Minus, Star, Slash,
    Equal, NotEqual, Less, Greater,
    Assign,
    LeftParen, RightParen,
    LeftBrace, RightBrace,
    Semicolon, Comma, Colon,
    EOF,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Token {
    pub token_type: TokenType,
    pub lexeme: String,
    pub line: usize,
    pub column: usize,
}

impl Token {
    pub fn new(token_type: TokenType, lexeme: String, line: usize, column: usize) -> Self {
        Self { token_type, lexeme, line, column }
    }
}

#[derive(Debug, Clone)]
pub struct Lexer {
    source: String,
    position: usize,
    line: usize,
    column: usize,
    keywords: HashMap<String, TokenType>,
}

impl Lexer {
    pub fn new(source: String) -> Self {
        let mut keywords = HashMap::new();
        for kw in &["let", "fn", "if", "else", "while", "return", "true", "false"] {
            keywords.insert(kw.to_string(), TokenType::Keyword(kw.to_string()));
        }
        
        Self { source, position: 0, line: 1, column: 1, keywords }
    }
    
    pub fn tokenize(&mut self) -> LanguageResult<Vec<Token>> {
        let mut tokens = Vec::new();
        
        while !self.is_at_end() {
            self.skip_whitespace();
            if self.is_at_end() { break; }
            
            let start_line = self.line;
            let start_col = self.column;
            
            match self.peek() {
                Some('a'..='z') | Some('A'..='Z') | Some('_') => {
                    tokens.push(self.read_identifier(start_line, start_col)?);
                }
                Some('0'..='9') => {
                    tokens.push(self.read_number(start_line, start_col)?);
                }
                Some('+') => { self.advance(); tokens.push(Token::new(TokenType::Plus, "+".into(), start_line, start_col)); }
                Some('-') => { self.advance(); tokens.push(Token::new(TokenType::Minus, "-".into(), start_line, start_col)); }
                Some('*') => { self.advance(); tokens.push(Token::new(TokenType::Star, "*".into(), start_line, start_col)); }
                Some('/') => { self.advance(); tokens.push(Token::new(TokenType::Slash, "/".into(), start_line, start_col)); }
                Some('=') => {
                    self.advance();
                    if self.peek() == Some('=') {
                        self.advance();
                        tokens.push(Token::new(TokenType::Equal, "==".into(), start_line, start_col));
                    } else {
                        tokens.push(Token::new(TokenType::Assign, "=".into(), start_line, start_col));
                    }
                }
                Some('(') => { self.advance(); tokens.push(Token::new(TokenType::LeftParen, "(".into(), start_line, start_col)); }
                Some(')') => { self.advance(); tokens.push(Token::new(TokenType::RightParen, ")".into(), start_line, start_col)); }
                Some('{') => { self.advance(); tokens.push(Token::new(TokenType::LeftBrace, "{".into(), start_line, start_col)); }
                Some('}') => { self.advance(); tokens.push(Token::new(TokenType::RightBrace, "}".into(), start_line, start_col)); }
                Some(';') => { self.advance(); tokens.push(Token::new(TokenType::Semicolon, ";".into(), start_line, start_col)); }
                Some(',') => { self.advance(); tokens.push(Token::new(TokenType::Comma, ",".into(), start_line, start_col)); }
                Some(':') => { self.advance(); tokens.push(Token::new(TokenType::Colon, ":".into(), start_line, start_col)); }
                Some(c) => return Err(ModelError::ParseError(format!("Unexpected char: {}", c))),
                None => break,
            }
        }
        
        tokens.push(Token::new(TokenType::EOF, "".into(), self.line, self.column));
        Ok(tokens)
    }
    
    fn peek(&self) -> Option<char> {
        self.source.chars().nth(self.position)
    }
    
    fn advance(&mut self) -> Option<char> {
        if let Some(ch) = self.peek() {
            self.position += 1;
            if ch == '\n' { self.line += 1; self.column = 1; } else { self.column += 1; }
            Some(ch)
        } else { None }
    }
    
    fn is_at_end(&self) -> bool {
        self.position >= self.source.len()
    }
    
    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_whitespace() { self.advance(); } else { break; }
        }
    }
    
    fn read_identifier(&mut self, line: usize, col: usize) -> LanguageResult<Token> {
        let start = self.position;
        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' { self.advance(); } else { break; }
        }
        let lexeme = self.source[start..self.position].to_string();
        let token_type = self.keywords.get(&lexeme).cloned().unwrap_or(TokenType::Identifier);
        Ok(Token::new(token_type, lexeme, line, col))
    }
    
    fn read_number(&mut self, line: usize, col: usize) -> LanguageResult<Token> {
        let start = self.position;
        while let Some(ch) = self.peek() {
            if ch.is_numeric() { self.advance(); } else { break; }
        }
        let lexeme = self.source[start..self.position].to_string();
        Ok(Token::new(TokenType::IntLiteral, lexeme, line, col))
    }
}

// ========== 抽象语法树 ==========

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ASTNode {
    Program(Vec<ASTNode>),
    VariableDeclaration { name: String, value: Box<ASTNode> },
    FunctionDeclaration { name: String, params: Vec<String>, body: Box<ASTNode> },
    BinaryOp { op: String, left: Box<ASTNode>, right: Box<ASTNode> },
    IntLiteral(i64),
    Identifier(String),
    Block(Vec<ASTNode>),
    NoOp,
}

// ========== 语法分析器 ==========

pub struct Parser {
    tokens: Vec<Token>,
    current: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, current: 0 }
    }
    
    pub fn parse(&mut self) -> LanguageResult<ASTNode> {
        let mut statements = Vec::new();
        while !self.is_at_end() {
            statements.push(self.parse_statement()?);
        }
        Ok(ASTNode::Program(statements))
    }
    
    fn parse_statement(&mut self) -> LanguageResult<ASTNode> {
        if let TokenType::Keyword(k) = &self.peek().token_type {
            if k == "let" { return self.parse_var_decl(); }
        }
        self.parse_expression()
    }
    
    fn parse_var_decl(&mut self) -> LanguageResult<ASTNode> {
        self.advance(); // 'let'
        let name = if let TokenType::Identifier = self.peek().token_type {
            self.advance().lexeme.clone()
        } else {
            return Err(ModelError::ParseError("Expected identifier".into()));
        };
        
        if !matches!(self.peek().token_type, TokenType::Assign) {
            return Err(ModelError::ParseError("Expected '='".into()));
        }
        self.advance();
        
        let value = Box::new(self.parse_expression()?);
        
        if matches!(self.peek().token_type, TokenType::Semicolon) {
            self.advance();
        }
        
        Ok(ASTNode::VariableDeclaration { name, value })
    }
    
    fn parse_expression(&mut self) -> LanguageResult<ASTNode> {
        self.parse_term()
    }
    
    fn parse_term(&mut self) -> LanguageResult<ASTNode> {
        let mut left = self.parse_primary()?;
        
        while matches!(self.peek().token_type, TokenType::Plus | TokenType::Minus) {
            let op = self.advance().lexeme.clone();
            let right = Box::new(self.parse_primary()?);
            left = ASTNode::BinaryOp { op, left: Box::new(left), right };
        }
        
        Ok(left)
    }
    
    fn parse_primary(&mut self) -> LanguageResult<ASTNode> {
        match &self.peek().token_type {
            TokenType::IntLiteral => {
                let token = self.advance();
                let value = token.lexeme.parse::<i64>()
                    .map_err(|_| ModelError::ParseError("Invalid integer".into()))?;
                Ok(ASTNode::IntLiteral(value))
            }
            TokenType::Identifier => {
                let name = self.advance().lexeme.clone();
                Ok(ASTNode::Identifier(name))
            }
            _ => Err(ModelError::ParseError(format!("Unexpected token: {:?}", self.peek()))),
        }
    }
    
    fn peek(&self) -> &Token {
        &self.tokens[self.current]
    }
    
    fn advance(&mut self) -> &Token {
        if !self.is_at_end() { self.current += 1; }
        &self.tokens[self.current - 1]
    }
    
    fn is_at_end(&self) -> bool {
        matches!(self.peek().token_type, TokenType::EOF)
    }
}

// ========== 类型注解 ==========

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TypeAnnotation {
    Int,
    Float,
    Bool,
    String,
    Void,
    Unknown,
}

impl fmt::Display for TypeAnnotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeAnnotation::Int => write!(f, "int"),
            TypeAnnotation::Float => write!(f, "float"),
            TypeAnnotation::Bool => write!(f, "bool"),
            TypeAnnotation::String => write!(f, "string"),
            TypeAnnotation::Void => write!(f, "void"),
            TypeAnnotation::Unknown => write!(f, "unknown"),
        }
    }
}

// ========== 符号表 ==========

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SymbolInfo {
    pub name: String,
    pub symbol_type: TypeAnnotation,
    pub is_initialized: bool,
}

// ========== 语义分析器 ==========

#[derive(Debug, Default)]
pub struct SemanticAnalyzer {
    symbol_table: HashMap<String, SymbolInfo>,
}

impl SemanticAnalyzer {
    pub fn new() -> Self {
        Self { symbol_table: HashMap::new() }
    }
    
    pub fn analyze(&mut self, ast: &ASTNode) -> LanguageResult<()> {
        self.analyze_node(ast)?;
        Ok(())
    }
    
    fn analyze_node(&mut self, node: &ASTNode) -> LanguageResult<TypeAnnotation> {
        match node {
            ASTNode::Program(stmts) => {
                for stmt in stmts { self.analyze_node(stmt)?; }
                Ok(TypeAnnotation::Void)
            }
            ASTNode::VariableDeclaration { name, value } => {
                let val_type = self.analyze_node(value)?;
                self.symbol_table.insert(name.clone(), SymbolInfo {
                    name: name.clone(),
                    symbol_type: val_type.clone(),
                    is_initialized: true,
                });
                Ok(val_type)
            }
            ASTNode::Identifier(name) => {
                self.symbol_table.get(name)
                    .map(|s| s.symbol_type.clone())
                    .ok_or_else(|| ModelError::SemanticError(format!("Undefined: {}", name)))
            }
            ASTNode::IntLiteral(_) => Ok(TypeAnnotation::Int),
            ASTNode::BinaryOp { left, right, .. } => {
                self.analyze_node(left)?;
                self.analyze_node(right)?;
                Ok(TypeAnnotation::Int)
            }
            _ => Ok(TypeAnnotation::Unknown),
        }
    }
    
    pub fn get_symbol_table(&self) -> &HashMap<String, SymbolInfo> {
        &self.symbol_table
    }
}

// ========== 语言模型引擎 ==========

pub struct LanguageModelEngine {
    source_code: String,
}

impl LanguageModelEngine {
    pub fn new(source_code: String) -> Self {
        Self { source_code }
    }
    
    pub fn compile(&self) -> LanguageResult<ASTNode> {
        let mut lexer = Lexer::new(self.source_code.clone());
        let tokens = lexer.tokenize()?;
        let mut parser = Parser::new(tokens);
        let ast = parser.parse()?;
        let mut analyzer = SemanticAnalyzer::new();
        analyzer.analyze(&ast)?;
        Ok(ast)
    }
    
    pub fn tokenize(&self) -> LanguageResult<Vec<Token>> {
        let mut lexer = Lexer::new(self.source_code.clone());
        lexer.tokenize()
    }
    
    pub fn parse(&self) -> LanguageResult<ASTNode> {
        let mut lexer = Lexer::new(self.source_code.clone());
        let tokens = lexer.tokenize()?;
        let mut parser = Parser::new(tokens);
        parser.parse()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_lexer() {
        let mut lexer = Lexer::new("let x = 42;".into());
        let tokens = lexer.tokenize().unwrap();
        assert!(tokens.len() > 0);
    }
    
    #[test]
    fn test_parser() {
        let engine = LanguageModelEngine::new("let x = 42;".into());
        let ast = engine.parse().unwrap();
        assert!(matches!(ast, ASTNode::Program(_)));
    }
}

