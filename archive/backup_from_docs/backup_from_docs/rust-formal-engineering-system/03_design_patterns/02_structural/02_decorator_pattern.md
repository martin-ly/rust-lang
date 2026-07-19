# 装饰器模式（Decorator Pattern）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [装饰器模式](#装饰器模式decorator-pattern)
  - [概述](#概述)
  - [问题场景](#问题场景)
  - [解决方案](#解决方案)
  - [Rust 实现](#rust-实现)
  - [实践示例](#实践示例)
  - [优缺点](#优缺点)
  - [参考资料](#参考资料)

---

## 概述

装饰器模式（Decorator Pattern）是一种结构型设计模式，它允许你通过将对象放入包含行为的特殊封装对象中来为原对象绑定新的行为。装饰器模式提供了比继承更有弹性的替代方案。

## 问题场景

假设我们需要为一个文本处理系统添加不同的格式化功能（加粗、斜体、下划线等），并且这些功能可以组合使用。

## 解决方案

使用装饰器模式，将格式化功能作为装饰器包装在文本对象周围：

```rust
// 组件 Trait
pub trait TextComponent {
    fn render(&self) -> String;
}

// 具体组件
pub struct PlainText {
    content: String,
}

impl PlainText {
    pub fn new(content: String) -> Self {
        PlainText { content }
    }
}

impl TextComponent for PlainText {
    fn render(&self) -> String {
        self.content.clone()
    }
}

// 装饰器基类
pub struct TextDecorator {
    component: Box<dyn TextComponent>,
}

impl TextDecorator {
    pub fn new(component: Box<dyn TextComponent>) -> Self {
        TextDecorator { component }
    }
}

impl TextComponent for TextDecorator {
    fn render(&self) -> String {
        self.component.render()
    }
}

// 具体装饰器
pub struct BoldDecorator {
    decorator: TextDecorator,
}

impl BoldDecorator {
    pub fn new(component: Box<dyn TextComponent>) -> Self {
        BoldDecorator {
            decorator: TextDecorator::new(component),
        }
    }
}

impl TextComponent for BoldDecorator {
    fn render(&self) -> String {
        format!("<b>{}</b>", self.decorator.render())
    }
}

pub struct ItalicDecorator {
    decorator: TextDecorator,
}

impl ItalicDecorator {
    pub fn new(component: Box<dyn TextComponent>) -> Self {
        ItalicDecorator {
            decorator: TextDecorator::new(component),
        }
    }
}

impl TextComponent for ItalicDecorator {
    fn render(&self) -> String {
        format!("<i>{}</i>", self.decorator.render())
    }
}

pub struct UnderlineDecorator {
    decorator: TextDecorator,
}

impl UnderlineDecorator {
    pub fn new(component: Box<dyn TextComponent>) -> Self {
        UnderlineDecorator {
            decorator: TextDecorator::new(component),
        }
    }
}

impl TextComponent for UnderlineDecorator {
    fn render(&self) -> String {
        format!("<u>{}</u>", self.decorator.render())
    }
}
```

## Rust 实现

### 使用组合

```rust
// 使用示例
let text = PlainText::new("Hello, World!".to_string());
let bold_text = BoldDecorator::new(Box::new(text));
let bold_italic_text = ItalicDecorator::new(Box::new(bold_text));
let decorated_text = UnderlineDecorator::new(Box::new(bold_italic_text));

println!("{}", decorated_text.render());
// 输出: <u><i><b>Hello, World!</b></i></u>
```

### 使用 Trait 对象

```rust
pub trait Coffee {
    fn cost(&self) -> f64;
    fn description(&self) -> String;
}

pub struct SimpleCoffee;

impl Coffee for SimpleCoffee {
    fn cost(&self) -> f64 {
        2.0
    }

    fn description(&self) -> String {
        "简单咖啡".to_string()
    }
}

pub struct CoffeeDecorator {
    coffee: Box<dyn Coffee>,
}

impl CoffeeDecorator {
    pub fn new(coffee: Box<dyn Coffee>) -> Self {
        CoffeeDecorator { coffee }
    }
}

impl Coffee for CoffeeDecorator {
    fn cost(&self) -> f64 {
        self.coffee.cost()
    }

    fn description(&self) -> String {
        self.coffee.description()
    }
}

pub struct MilkDecorator {
    decorator: CoffeeDecorator,
}

impl MilkDecorator {
    pub fn new(coffee: Box<dyn Coffee>) -> Self {
        MilkDecorator {
            decorator: CoffeeDecorator::new(coffee),
        }
    }
}

impl Coffee for MilkDecorator {
    fn cost(&self) -> f64 {
        self.decorator.cost() + 0.5
    }

    fn description(&self) -> String {
        format!("{}, 牛奶", self.decorator.description())
    }
}

pub struct SugarDecorator {
    decorator: CoffeeDecorator,
}

impl SugarDecorator {
    pub fn new(coffee: Box<dyn Coffee>) -> Self {
        SugarDecorator {
            decorator: CoffeeDecorator::new(coffee),
        }
    }
}

impl Coffee for SugarDecorator {
    fn cost(&self) -> f64 {
        self.decorator.cost() + 0.2
    }

    fn description(&self) -> String {
        format!("{}, 糖", self.decorator.description())
    }
}
```

## 实践示例

### 示例 1：HTTP 中间件装饰器

```rust
use std::future::Future;
use std::pin::Pin;

pub type Handler = Box<dyn Fn(Request) -> Pin<Box<dyn Future<Output = Response> + Send>> + Send + Sync>;

pub struct Request {
    // 请求数据
}

pub struct Response {
    // 响应数据
}

pub trait Middleware {
    fn handle(&self, request: Request, next: Handler) -> Pin<Box<dyn Future<Output = Response> + Send>>;
}

pub struct LoggingMiddleware;

impl Middleware for LoggingMiddleware {
    fn handle(&self, request: Request, next: Handler) -> Pin<Box<dyn Future<Output = Response> + Send>> {
        Box::pin(async move {
            println!("请求开始: {:?}", request);
            let response = next(request).await;
            println!("请求完成: {:?}", response);
            response
        })
    }
}

pub struct AuthMiddleware;

impl Middleware for AuthMiddleware {
    fn handle(&self, request: Request, next: Handler) -> Pin<Box<dyn Future<Output = Response> + Send>> {
        Box::pin(async move {
            // 验证逻辑
            next(request).await
        })
    }
}
```

### 示例 2：缓存装饰器

```rust
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::{Arc, RwLock};

pub trait DataSource {
    fn get_data(&self, key: &str) -> Option<String>;
}

pub struct DatabaseSource;

impl DataSource for DatabaseSource {
    fn get_data(&self, key: &str) -> Option<String> {
        // 从数据库获取数据
        Some(format!("数据: {}", key))
    }
}

pub struct CachedDataSource {
    source: Box<dyn DataSource>,
    cache: Arc<RwLock<HashMap<String, String>>>,
}

impl CachedDataSource {
    pub fn new(source: Box<dyn DataSource>) -> Self {
        CachedDataSource {
            source,
            cache: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

impl DataSource for CachedDataSource {
    fn get_data(&self, key: &str) -> Option<String> {
        // 先检查缓存
        {
            let cache = self.cache.read().unwrap();
            if let Some(value) = cache.get(key) {
                return Some(value.clone());
            }
        }

        // 从源获取数据
        if let Some(value) = self.source.get_data(key) {
            // 存入缓存
            let mut cache = self.cache.write().unwrap();
            cache.insert(key.to_string(), value.clone());
            Some(value)
        } else {
            None
        }
    }
}
```

## 优缺点

### 优点

1. **灵活性**：可以在运行时动态组合功能
2. **单一职责**：每个装饰器只负责一个功能
3. **开闭原则**：可以添加新装饰器而不修改现有代码

### 缺点

1. **复杂性**：可能产生大量小类
2. **调试困难**：装饰器链可能难以调试
3. **性能开销**：多层装饰可能带来性能开销

## 参考资料

- [结构型模式索引](./00_index.md)
- [设计模式索引](../00_index.md)
- [适配器模式](./01_adapter_pattern.md)

---

**导航**:
- 返回索引: [`00_index.md`](./00_index.md)
- 返回设计模式: [`../00_index.md`](../00_index.md)
