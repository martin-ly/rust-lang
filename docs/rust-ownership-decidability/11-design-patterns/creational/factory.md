# Factory Pattern in Rust

> **设计模式**: 创建型模式
> **难度**: 🟢 简单
> **应用场景**: 对象创建的封装与多态

---

## 📑 目录
>
- [Factory Pattern in Rust](#factory-pattern-in-rust)
  - [📑 目录](#-目录)
  - [概念](#概念)
  - [基础实现](#基础实现)
    - [简单工厂](#简单工厂)
    - [工厂方法](#工厂方法)
  - [抽象工厂](#抽象工厂)
  - [形式化定义](#形式化定义)
  - [使用泛型的零成本抽象](#使用泛型的零成本抽象)
  - [相关概念](#相关概念)

## 概念
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

工厂模式定义一个创建对象的接口，让子类决定实例化哪个类。工厂方法使类的实例化延迟到子类。

---

## 基础实现
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 简单工厂
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```rust
pub trait Animal {
    fn speak(&self) -> String;
    fn name(&self) -> &str;
}

pub struct Dog {
    name: String,
}

impl Animal for Dog {
    fn speak(&self) -> String {
        "Woof!".to_string()
    }
    fn name(&self) -> &str {
        &self.name
    }
}

pub struct Cat {
    name: String,
}

impl Animal for Cat {
    fn speak(&self) -> String {
        "Meow!".to_string()
    }
    fn name(&self) -> &str {
        &self.name
    }
}

pub enum AnimalType {
    Dog,
    Cat,
}

// 简单工厂函数
pub fn create_animal(animal_type: AnimalType, name: &str) -> Box<dyn Animal> {
    match animal_type {
        AnimalType::Dog => Box::new(Dog {
            name: name.to_string(),
        }),
        AnimalType::Cat => Box::new(Cat {
            name: name.to_string(),
        }),
    }
}

// 使用
let dog = create_animal(AnimalType::Dog, "Buddy");
let cat = create_animal(AnimalType::Cat, "Whiskers");
```

### 工厂方法

```rust
pub trait Parser {
    fn parse(&self, input: &str) -> Result<Vec<Token>, ParseError>;
}

pub struct JsonParser;
pub struct YamlParser;

impl Parser for JsonParser {
    fn parse(&self, input: &str) -> Result<Vec<Token>, ParseError> {
        // JSON 解析逻辑
        Ok(vec![])
    }
}

impl Parser for YamlParser {
    fn parse(&self, input: &str) -> Result<Vec<Token>, ParseError> {
        // YAML 解析逻辑
        Ok(vec![])
    }
}

// 工厂 trait
pub trait ParserFactory {
    fn create_parser(&self) -> Box<dyn Parser>;
}

pub struct JsonParserFactory;
pub struct YamlParserFactory;

impl ParserFactory for JsonParserFactory {
    fn create_parser(&self) -> Box<dyn Parser> {
        Box::new(JsonParser)
    }
}

impl ParserFactory for YamlParserFactory {
    fn create_parser(&self) -> Box<dyn Parser> {
        Box::new(YamlParser)
    }
}

// 客户端代码
fn process_data(factory: &dyn ParserFactory, data: &str) -> Result<(), ParseError> {
    let parser = factory.create_parser();
    let tokens = parser.parse(data)?;
    println!("Parsed {} tokens", tokens.len());
    Ok(())
}
```

---

## 抽象工厂

```rust
// UI 组件族
pub trait Button {
    fn render(&self);
    fn on_click(&self, callback: Box<dyn Fn()>);
}

pub trait Checkbox {
    fn render(&self);
    fn toggle(&mut self);
}

// 抽象工厂
trait GUIFactory {
    fn create_button(&self, label: &str) -> Box<dyn Button>;
    fn create_checkbox(&self, label: &str) -> Box<dyn Checkbox>;
}

// Windows 实现
struct WindowsButton;
impl Button for WindowsButton {
    fn render(&self) { println!("Rendering Windows button"); }
    fn on_click(&self, _cb: Box<dyn Fn()>) {}
}

struct WindowsCheckbox;
impl Checkbox for WindowsCheckbox {
    fn render(&self) { println!("Rendering Windows checkbox"); }
    fn toggle(&mut self) {}
}

struct WindowsFactory;
impl GUIFactory for WindowsFactory {
    fn create_button(&self, _label: &str) -> Box<dyn Button> {
        Box::new(WindowsButton)
    }
    fn create_checkbox(&self, _label: &str) -> Box<dyn Checkbox> {
        Box::new(WindowsCheckbox)
    }
}

// macOS 实现
struct MacButton;
impl Button for MacButton {
    fn render(&self) { println!("Rendering Mac button"); }
    fn on_click(&self, _cb: Box<dyn Fn()>) {}
}

struct MacCheckbox;
impl Checkbox for MacCheckbox {
    fn render(&self) { println!("Rendering Mac checkbox"); }
    fn toggle(&mut self) {}
}

struct MacFactory;
impl GUIFactory for MacFactory {
    fn create_button(&self, _label: &str) -> Box<dyn Button> {
        Box::new(MacButton)
    }
    fn create_checkbox(&self, _label: &str) -> Box<dyn Checkbox> {
        Box::new(MacCheckbox)
    }
}
```

---

## 形式化定义

```
Factory<T> = (args: Args) → T

性质:
  1. 封装性: 客户端不直接调用 T::new()
  2. 多态性: 可以返回不同的 T 实现
  3. 延迟绑定: 类型决定在运行时
```

---

## 使用泛型的零成本抽象

```rust
// 避免动态分派
pub trait Factory<T> {
    fn create(&self) -> T;
}

pub struct ProductA;
pub struct ProductB;

pub struct FactoryA;
impl Factory<ProductA> for FactoryA {
    fn create(&self) -> ProductA {
        ProductA
    }
}

// 编译期单态化，零运行时开销
fn use_factory<F, T>(factory: F) -> T
where
    F: Factory<T>,
{
    factory.create()
}
```

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念

- [creational 目录](./README.md)


---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Design Pattern]**

> **[来源: Rust API Guidelines]**

> **[来源: Gang of Four - Design Patterns]**

> **[来源: ACM - Software Design Patterns]**
