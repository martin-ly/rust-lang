# 工厂模式（Factory Pattern）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [工厂模式](#工厂模式factory-pattern)
  - [概述](#概述)
  - [问题场景](#问题场景)
  - [解决方案](#解决方案)
  - [Rust 实现](#rust-实现)
  - [实践示例](#实践示例)
  - [优缺点](#优缺点)
  - [参考资料](#参考资料)

---

## 概述

工厂模式（Factory Pattern）是一种创建型设计模式，它提供了一种创建对象的最佳方式。在工厂模式中，我们在创建对象时不会对客户端暴露创建逻辑，而是通过使用一个共同的接口来指向新创建的对象。

## 问题场景

假设我们需要创建不同类型的数据库连接（MySQL、PostgreSQL、SQLite），并且希望客户端代码不需要知道具体的实现细节。

## 解决方案

使用工厂模式，将对象创建逻辑封装在工厂类中：

```rust
// 产品 Trait
pub trait DatabaseConnection {
    fn connect(&self) -> Result<(), String>;
    fn execute_query(&self, query: &str) -> Result<Vec<String>, String>;
    fn close(&self) -> Result<(), String>;
}

// 具体产品
pub struct MySQLConnection {
    host: String,
    port: u16,
    database: String,
}

impl MySQLConnection {
    pub fn new(host: String, port: u16, database: String) -> Self {
        MySQLConnection { host, port, database }
    }
}

impl DatabaseConnection for MySQLConnection {
    fn connect(&self) -> Result<(), String> {
        println!("连接到 MySQL: {}:{}/{}", self.host, self.port, self.database);
        Ok(())
    }

    fn execute_query(&self, query: &str) -> Result<Vec<String>, String> {
        println!("执行 MySQL 查询: {}", query);
        Ok(vec!["结果1".to_string(), "结果2".to_string()])
    }

    fn close(&self) -> Result<(), String> {
        println!("关闭 MySQL 连接");
        Ok(())
    }
}

pub struct PostgreSQLConnection {
    host: String,
    port: u16,
    database: String,
}

impl PostgreSQLConnection {
    pub fn new(host: String, port: u16, database: String) -> Self {
        PostgreSQLConnection { host, port, database }
    }
}

impl DatabaseConnection for PostgreSQLConnection {
    fn connect(&self) -> Result<(), String> {
        println!("连接到 PostgreSQL: {}:{}/{}", self.host, self.port, self.database);
        Ok(())
    }

    fn execute_query(&self, query: &str) -> Result<Vec<String>, String> {
        println!("执行 PostgreSQL 查询: {}", query);
        Ok(vec!["结果1".to_string(), "结果2".to_string()])
    }

    fn close(&self) -> Result<(), String> {
        println!("关闭 PostgreSQL 连接");
        Ok(())
    }
}
```

## Rust 实现

### 简单工厂

```rust
pub enum DatabaseType {
    MySQL,
    PostgreSQL,
    SQLite,
}

pub struct DatabaseFactory;

impl DatabaseFactory {
    pub fn create_connection(
        db_type: DatabaseType,
        host: String,
        port: u16,
        database: String,
    ) -> Box<dyn DatabaseConnection> {
        match db_type {
            DatabaseType::MySQL => {
                Box::new(MySQLConnection::new(host, port, database))
            }
            DatabaseType::PostgreSQL => {
                Box::new(PostgreSQLConnection::new(host, port, database))
            }
            DatabaseType::SQLite => {
                Box::new(SQLiteConnection::new(database))
            }
        }
    }
}

// 使用
let connection = DatabaseFactory::create_connection(
    DatabaseType::MySQL,
    "localhost".to_string(),
    3306,
    "mydb".to_string(),
);
```

### 工厂方法模式

```rust
pub trait DatabaseFactory {
    fn create_connection(&self, config: DatabaseConfig) -> Box<dyn DatabaseConnection>;
}

pub struct DatabaseConfig {
    pub host: String,
    pub port: u16,
    pub database: String,
}

pub struct MySQLFactory;

impl DatabaseFactory for MySQLFactory {
    fn create_connection(&self, config: DatabaseConfig) -> Box<dyn DatabaseConnection> {
        Box::new(MySQLConnection::new(config.host, config.port, config.database))
    }
}

pub struct PostgreSQLFactory;

impl DatabaseFactory for PostgreSQLFactory {
    fn create_connection(&self, config: DatabaseConfig) -> Box<dyn DatabaseConnection> {
        Box::new(PostgreSQLConnection::new(config.host, config.port, config.database))
    }
}
```

### 抽象工厂模式

```rust
pub trait DatabaseFactory {
    fn create_connection(&self) -> Box<dyn DatabaseConnection>;
    fn create_query_builder(&self) -> Box<dyn QueryBuilder>;
}

pub trait QueryBuilder {
    fn select(&mut self, columns: Vec<String>) -> &mut Self;
    fn from(&mut self, table: String) -> &mut Self;
    fn build(&self) -> String;
}

pub struct MySQLFactory;

impl DatabaseFactory for MySQLFactory {
    fn create_connection(&self) -> Box<dyn DatabaseConnection> {
        Box::new(MySQLConnection::new(
            "localhost".to_string(),
            3306,
            "mydb".to_string(),
        ))
    }

    fn create_query_builder(&self) -> Box<dyn QueryBuilder> {
        Box::new(MySQLQueryBuilder::new())
    }
}

pub struct MySQLQueryBuilder {
    columns: Vec<String>,
    table: Option<String>,
}

impl MySQLQueryBuilder {
    pub fn new() -> Self {
        MySQLQueryBuilder {
            columns: Vec::new(),
            table: None,
        }
    }
}

impl QueryBuilder for MySQLQueryBuilder {
    fn select(&mut self, columns: Vec<String>) -> &mut Self {
        self.columns = columns;
        self
    }

    fn from(&mut self, table: String) -> &mut Self {
        self.table = Some(table);
        self
    }

    fn build(&self) -> String {
        format!(
            "SELECT {} FROM {}",
            self.columns.join(", "),
            self.table.as_ref().unwrap()
        )
    }
}
```

## 实践示例

### 示例 1：日志工厂

```rust
pub trait Logger {
    fn log(&self, level: LogLevel, message: &str);
}

pub enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
}

pub struct FileLogger {
    file_path: String,
}

impl FileLogger {
    pub fn new(file_path: String) -> Self {
        FileLogger { file_path }
    }
}

impl Logger for FileLogger {
    fn log(&self, level: LogLevel, message: &str) {
        println!("[文件日志] {:?}: {} -> {}", level, message, self.file_path);
    }
}

pub struct ConsoleLogger;

impl Logger for ConsoleLogger {
    fn log(&self, level: LogLevel, message: &str) {
        println!("[控制台日志] {:?}: {}", level, message);
    }
}

pub enum LoggerType {
    File(String),
    Console,
}

pub struct LoggerFactory;

impl LoggerFactory {
    pub fn create_logger(logger_type: LoggerType) -> Box<dyn Logger> {
        match logger_type {
            LoggerType::File(path) => Box::new(FileLogger::new(path)),
            LoggerType::Console => Box::new(ConsoleLogger),
        }
    }
}
```

### 示例 2：支付网关工厂

```rust
use async_trait::async_trait;

#[async_trait]
pub trait PaymentGateway {
    async fn process_payment(&self, amount: f64) -> Result<String, String>;
}

pub struct StripeGateway {
    api_key: String,
}

impl StripeGateway {
    pub fn new(api_key: String) -> Self {
        StripeGateway { api_key }
    }
}

#[async_trait]
impl PaymentGateway for StripeGateway {
    async fn process_payment(&self, amount: f64) -> Result<String, String> {
        Ok(format!("Stripe 支付: {} 美元", amount))
    }
}

pub struct PayPalGateway {
    client_id: String,
}

impl PayPalGateway {
    pub fn new(client_id: String) -> Self {
        PayPalGateway { client_id }
    }
}

#[async_trait]
impl PaymentGateway for PayPalGateway {
    async fn process_payment(&self, amount: f64) -> Result<String, String> {
        Ok(format!("PayPal 支付: {} 美元", amount))
    }
}

pub enum PaymentProvider {
    Stripe(String),
    PayPal(String),
}

pub struct PaymentGatewayFactory;

impl PaymentGatewayFactory {
    pub fn create_gateway(provider: PaymentProvider) -> Box<dyn PaymentGateway> {
        match provider {
            PaymentProvider::Stripe(api_key) => {
                Box::new(StripeGateway::new(api_key))
            }
            PaymentProvider::PayPal(client_id) => {
                Box::new(PayPalGateway::new(client_id))
            }
        }
    }
}
```

## 优缺点

### 优点

1. **解耦**：将对象创建与使用分离
2. **扩展性**：易于添加新产品类型
3. **单一职责**：工厂类只负责创建对象

### 缺点

1. **复杂性**：增加代码复杂度
2. **抽象层**：可能过度设计

## 参考资料

- [创建型模式索引](./00_index.md)
- [设计模式索引](../00_index.md)

---

**导航**:
- 返回索引: [`00_index.md`](./00_index.md)
- 返回设计模式: [`../00_index.md`](../00_index.md)
