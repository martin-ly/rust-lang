# Factory Pattern in Rust

> **设计模式**: 创建型模式
> **难度**: 🟢 简单
> **应用场景**: 对象创建的封装与多态

---

## 概念

工厂模式定义一个创建对象的接口，让子类决定实例化哪个类。工厂方法使类的实例化延迟到子类。

---

## 基础实现

### 简单工厂

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
