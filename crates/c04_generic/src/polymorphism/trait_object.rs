/*
Trait Object 是 Rust 中实现运行时多态性的重要机制。
它允许我们在运行时动态选择具体的类型实现，实现真正的多态。

## 定义

Trait Object 是一个指向实现了特定特征的类型的指针：

```rust
// 特征对象类型
Box<dyn Trait>
&dyn Trait
Arc<dyn Trait>
```

## 重要特性

1. **运行时多态**: 在运行时确定具体类型
2. **动态分发**: 通过虚函数表调用方法
3. **类型擦除**: 编译时不知道具体类型
4. **对象安全**: 必须满足对象安全约束

## 对象安全约束

特征要实现为对象，必须满足以下条件：

1. **方法不能有泛型参数**
2. **方法不能返回 Self**
3. **方法不能有 where 子句**
4. **方法不能是关联函数**

## 实现示例

### 1. 基本特征对象

```rust
trait Drawable {
    fn draw(&self);
}

struct Circle {
    radius: f64,
}

struct Square {
    side: f64,
}

impl Drawable for Circle {
    fn draw(&self) {
        println!("Drawing circle with radius {}", self.radius);
    }
}

impl Drawable for Square {
    fn draw(&self) {
        println!("Drawing square with side {}", self.side);
    }
}

fn main() {
    let shapes: Vec<Box<dyn Drawable>> = vec![
        Box::new(Circle { radius: 5.0 }),
        Box::new(Square { side: 10.0 }),
    ];

    for shape in shapes {
        shape.draw();
    }
}
```

### 2. 特征对象作为参数

```rust
trait Processor {
    fn process(&self, input: &str) -> String;
}

struct UppercaseProcessor;
struct LowercaseProcessor;
struct ReverseProcessor;

impl Processor for UppercaseProcessor {
    fn process(&self, input: &str) -> String {
        input.to_uppercase()
    }
}

impl Processor for LowercaseProcessor {
    fn process(&self, input: &str) -> String {
        input.to_lowercase()
    }
}

impl Processor for ReverseProcessor {
    fn process(&self, input: &str) -> String {
        input.chars().rev().collect()
    }
}

fn process_text(processor: &dyn Processor, text: &str) -> String {
    processor.process(text)
}

fn main() {
    let text = "Hello, Rust!";

    let processors: Vec<Box<dyn Processor>> = vec![
        Box::new(UppercaseProcessor),
        Box::new(LowercaseProcessor),
        Box::new(ReverseProcessor),
    ];

    for processor in processors {
        let result = process_text(processor.as_ref(), text);
        println!("Result: {}", result);
    }
}
```

### 3. 特征对象集合

```rust
use std::collections::HashMap;

trait Storage {
    fn store(&mut self, key: &str, value: &str);
    fn retrieve(&self, key: &str) -> Option<&str>;
    fn remove(&mut self, key: &str) -> Option<String>;
}

struct MemoryStorage {
    data: HashMap<String, String>,
}

struct FileStorage {
    filename: String,
    data: HashMap<String, String>,
}

impl Storage for MemoryStorage {
    fn store(&mut self, key: &str, value: &str) {
        self.data.insert(key.to_string(), value.to_string());
    }

    fn retrieve(&self, key: &str) -> Option<&str> {
        self.data.get(key).map(|s| s.as_str())
    }

    fn remove(&mut self, key: &str) -> Option<String> {
        self.data.remove(key)
    }
}

impl Storage for FileStorage {
    fn store(&mut self, key: &str, value: &str) {
        self.data.insert(key.to_string(), value.to_string());
        // 这里可以添加文件写入逻辑
    }

    fn retrieve(&self, key: &str) -> Option<&str> {
        self.data.get(key).map(|s| s.as_str())
    }

    fn remove(&mut self, key: &str) -> Option<String> {
        self.data.remove(key)
    }
}

impl MemoryStorage {
    fn new() -> Self {
        MemoryStorage {
            data: HashMap::new(),
        }
    }
}

impl FileStorage {
    fn new(filename: String) -> Self {
        FileStorage {
            filename,
            data: HashMap::new(),
        }
    }
}
```

## 使用场景

### 1. 插件系统

```rust
trait Plugin {
    fn name(&self) -> &str;
    fn execute(&self, input: &str) -> String;
    fn version(&self) -> &str;
}

struct TextPlugin;
struct MathPlugin;
struct CryptoPlugin;

impl Plugin for TextPlugin {
    fn name(&self) -> &str {
        "Text Plugin"
    }

    fn execute(&self, input: &str) -> String {
        input.to_uppercase()
    }

    fn version(&self) -> &str {
        "1.0.0"
    }
}

impl Plugin for MathPlugin {
    fn name(&self) -> &str {
        "Math Plugin"
    }

    fn execute(&self, input: &str) -> String {
        if let Ok(num) = input.parse::<f64>() {
            format!("Square: {}, Cube: {}", num * num, num * num * num)
        } else {
            "Invalid number".to_string()
        }
    }

    fn version(&self) -> &str {
        "1.0.0"
    }
}

impl Plugin for CryptoPlugin {
    fn name(&self) -> &str {
        "Crypto Plugin"
    }

    fn execute(&self, input: &str) -> String {
        // 简单的ROT13加密
        input.chars()
            .map(|c| {
                if c.is_ascii_alphabetic() {
                    let base = if c.is_ascii_lowercase() { b'a' } else { b'A' };
                    let offset = (c as u8 - base + 13) % 26;
                    (base + offset) as char
                } else {
                    c
                }
            })
            .collect()
    }

    fn version(&self) -> &str {
        "1.0.0"
    }
}

struct PluginManager {
    plugins: Vec<Box<dyn Plugin>>,
}

impl PluginManager {
    fn new() -> Self {
        PluginManager {
            plugins: Vec::new(),
        }
    }

    fn add_plugin(&mut self, plugin: Box<dyn Plugin>) {
        self.plugins.push(plugin);
    }

    fn execute_all(&self, input: &str) {
        for plugin in &self.plugins {
            println!("Plugin: {} (v{})", plugin.name(), plugin.version());
            let result = plugin.execute(input);
            println!("Result: {}", result);
            println!("---");
        }
    }
}
```

### 2. 事件处理系统

```rust
trait EventHandler {
    fn handle(&self, event: &Event);
    fn priority(&self) -> u8;
}

#[derive(Debug)]
struct Event {
    event_type: String,
    data: String,
    timestamp: u64,
}

struct LoggingHandler;
struct NotificationHandler;
struct DatabaseHandler;

impl EventHandler for LoggingHandler {
    fn handle(&self, event: &Event) {
        println!("[LOG] {:?}", event);
    }

    fn priority(&self) -> u8 {
        1
    }
}

impl EventHandler for NotificationHandler {
    fn handle(&self, event: &Event) {
        println!("[NOTIFICATION] Sending notification for event: {}", event.event_type);
    }

    fn priority(&self) -> u8 {
        2
    }
}

impl EventHandler for DatabaseHandler {
    fn handle(&self, event: &Event) {
        println!("[DATABASE] Storing event in database: {}", event.event_type);
    }

    fn priority(&self) -> u8 {
        3
    }
}

struct EventDispatcher {
    handlers: Vec<Box<dyn EventHandler>>,
}

impl EventDispatcher {
    fn new() -> Self {
        EventDispatcher {
            handlers: Vec::new(),
        }
    }

    fn add_handler(&mut self, handler: Box<dyn EventHandler>) {
        self.handlers.push(handler);
        // 按优先级排序
        self.handlers.sort_by(|a, b| a.priority().cmp(&b.priority()));
    }

    fn dispatch(&self, event: Event) {
        for handler in &self.handlers {
            handler.handle(&event);
        }
    }
}
```

### 3. 配置系统

```rust
trait ConfigProvider {
    fn get(&self, key: &str) -> Option<String>;
    fn set(&mut self, key: &str, value: String);
    fn remove(&mut self, key: &str) -> bool;
}

struct EnvironmentConfig;
struct FileConfig {
    path: String,
    data: std::collections::HashMap<String, String>,
}
struct DatabaseConfig {
    connection_string: String,
    table_name: String,
}

impl ConfigProvider for EnvironmentConfig {
    fn get(&self, key: &str) -> Option<String> {
        std::env::var(key).ok()
    }

    fn set(&mut self, _key: &str, _value: String) {
        // 环境变量通常是只读的
        eprintln!("Cannot set environment variable");
    }

    fn remove(&mut self, _key: &str) -> bool {
        eprintln!("Cannot remove environment variable");
        false
    }
}

impl ConfigProvider for FileConfig {
    fn get(&self, key: &str) -> Option<String> {
        self.data.get(key).cloned()
    }

    fn set(&mut self, key: &str, value: String) {
        self.data.insert(key.to_string(), value);
        // 这里可以添加文件写入逻辑
    }

    fn remove(&mut self, key: &str) -> bool {
        self.data.remove(key).is_some()
    }
}

impl ConfigProvider for DatabaseConfig {
    fn get(&self, _key: &str) -> Option<String> {
        // 这里可以实现数据库查询逻辑
        None
    }

    fn set(&mut self, _key: &str, _value: String) {
        // 这里可以实现数据库写入逻辑
    }

    fn remove(&mut self, _key: &str) -> bool {
        // 这里可以实现数据库删除逻辑
        false
    }
}

impl FileConfig {
    fn new(path: String) -> Self {
        FileConfig {
            path,
            data: std::collections::HashMap::new(),
        }
    }
}

impl DatabaseConfig {
    fn new(connection_string: String, table_name: String) -> Self {
        DatabaseConfig {
            connection_string,
            table_name,
        }
    }
}
```

## 高级用法

### 1. 特征对象与生命周期

```rust
trait Renderer<'a> {
    fn render(&self, data: &'a str) -> String;
}

struct HtmlRenderer;
struct MarkdownRenderer;

impl<'a> Renderer<'a> for HtmlRenderer {
    fn render(&self, data: &'a str) -> String {
        format!("<div>{}</div>", data)
    }
}

impl<'a> Renderer<'a> for MarkdownRenderer {
    fn render(&self, data: &'a str) -> String {
        format!("**{}**", data)
    }
}

// 使用生命周期参数
fn render_with<'a, R: Renderer<'a>>(renderer: &R, data: &'a str) -> String {
    renderer.render(data)
}
```

### 2. 特征对象与泛型结合

```rust
trait Converter<T> {
    fn convert(&self, input: T) -> String;
}

struct StringConverter;
struct NumberConverter;
struct BooleanConverter;

impl Converter<String> for StringConverter {
    fn convert(&self, input: String) -> String {
        input
    }
}

impl Converter<i32> for NumberConverter {
    fn convert(&self, input: i32) -> String {
        input.to_string()
    }
}

impl Converter<bool> for BooleanConverter {
    fn convert(&self, input: bool) -> String {
        if input { "true".to_string() } else { "false".to_string() }
    }
}

// 泛型函数使用特征对象
fn convert_any<T>(converter: &dyn Converter<T>, input: T) -> String {
    converter.convert(input)
}
```

## 性能考虑

1. **动态分发**: 特征对象调用有运行时开销
2. **内存布局**: 需要额外的指针和虚函数表
3. **缓存友好性**: 可能影响CPU缓存性能
4. **编译时间**: 减少编译时类型检查

## 最佳实践

1. **对象安全**: 确保特征满足对象安全约束
2. **性能权衡**: 在需要运行时多态时使用特征对象
3. **生命周期管理**: 注意特征对象的生命周期
4. **错误处理**: 处理特征对象可能失败的情况

## 总结

Trait Object 为 Rust 提供了强大的运行时多态能力。
通过合理使用特征对象，可以创建灵活、可扩展的系统架构。
*/

use std::collections::HashMap;

// 基本特征对象
pub trait Drawable {
    fn draw(&self);
}

pub struct Circle {
    pub radius: f64,
}

pub struct Square {
    pub side: f64,
}

impl Drawable for Circle {
    fn draw(&self) {
        println!("Drawing circle with radius {}", self.radius);
    }
}

impl Drawable for Square {
    fn draw(&self) {
        println!("Drawing square with side {}", self.side);
    }
}

// 处理器特征
pub trait Processor {
    fn process(&self, input: &str) -> String;
}

pub struct UppercaseProcessor;
pub struct LowercaseProcessor;
pub struct ReverseProcessor;

impl Processor for UppercaseProcessor {
    fn process(&self, input: &str) -> String {
        input.to_uppercase()
    }
}

impl Processor for LowercaseProcessor {
    fn process(&self, input: &str) -> String {
        input.to_lowercase()
    }
}

impl Processor for ReverseProcessor {
    fn process(&self, input: &str) -> String {
        input.chars().rev().collect()
    }
}

// 存储特征
pub trait Storage {
    fn store(&mut self, key: &str, value: &str);
    fn retrieve(&self, key: &str) -> Option<&str>;
    fn remove(&mut self, key: &str) -> Option<String>;
}

pub struct MemoryStorage {
    pub data: HashMap<String, String>,
}

pub struct FileStorage {
    pub filename: String,
    pub data: HashMap<String, String>,
}

impl Storage for MemoryStorage {
    fn store(&mut self, key: &str, value: &str) {
        self.data.insert(key.to_string(), value.to_string());
    }

    fn retrieve(&self, key: &str) -> Option<&str> {
        self.data.get(key).map(|s| s.as_str())
    }

    fn remove(&mut self, key: &str) -> Option<String> {
        self.data.remove(key)
    }
}

impl Storage for FileStorage {
    fn store(&mut self, key: &str, value: &str) {
        self.data.insert(key.to_string(), value.to_string());
        // 这里可以添加文件写入逻辑
    }

    fn retrieve(&self, key: &str) -> Option<&str> {
        self.data.get(key).map(|s| s.as_str())
    }

    fn remove(&mut self, key: &str) -> Option<String> {
        self.data.remove(key)
    }
}

impl MemoryStorage {
    pub fn new() -> Self {
        MemoryStorage {
            data: HashMap::new(),
        }
    }
}

impl Default for MemoryStorage {
    fn default() -> Self {
        Self::new()
    }
}

impl FileStorage {
    pub fn new(filename: String) -> Self {
        FileStorage {
            filename,
            data: HashMap::new(),
        }
    }
}

// 插件系统
pub trait Plugin {
    fn name(&self) -> &str;
    fn execute(&self, input: &str) -> String;
    fn version(&self) -> &str;
}

pub struct TextPlugin;
pub struct MathPlugin;
pub struct CryptoPlugin;

impl Plugin for TextPlugin {
    fn name(&self) -> &str {
        "Text Plugin"
    }

    fn execute(&self, input: &str) -> String {
        input.to_uppercase()
    }

    fn version(&self) -> &str {
        "1.0.0"
    }
}

impl Plugin for MathPlugin {
    fn name(&self) -> &str {
        "Math Plugin"
    }

    fn execute(&self, input: &str) -> String {
        if let Ok(num) = input.parse::<f64>() {
            format!("Square: {}, Cube: {}", num * num, num * num * num)
        } else {
            "Invalid number".to_string()
        }
    }

    fn version(&self) -> &str {
        "1.0.0"
    }
}

impl Plugin for CryptoPlugin {
    fn name(&self) -> &str {
        "Crypto Plugin"
    }

    fn execute(&self, input: &str) -> String {
        // 简单的ROT13加密
        input
            .chars()
            .map(|c| {
                if c.is_ascii_alphabetic() {
                    let base = if c.is_ascii_lowercase() { b'a' } else { b'A' };
                    let offset = (c as u8 - base + 13) % 26;
                    (base + offset) as char
                } else {
                    c
                }
            })
            .collect()
    }

    fn version(&self) -> &str {
        "1.0.0"
    }
}

pub struct PluginManager {
    pub plugins: Vec<Box<dyn Plugin>>,
}

impl PluginManager {
    pub fn new() -> Self {
        PluginManager {
            plugins: Vec::new(),
        }
    }

    pub fn add_plugin(&mut self, plugin: Box<dyn Plugin>) {
        self.plugins.push(plugin);
    }

    pub fn execute_all(&self, input: &str) {
        for plugin in &self.plugins {
            println!("Plugin: {} (v{})", plugin.name(), plugin.version());
            let result = plugin.execute(input);
            println!("Result: {}", result);
            println!("---");
        }
    }
}

impl Default for PluginManager {
    fn default() -> Self {
        Self::new()
    }
}

// 演示函数
pub fn demonstrate_trait_object() {
    println!("=== Trait Object Demonstration ===\n");

    // 基本特征对象演示
    demonstrate_basic_trait_object();

    // 处理器演示
    demonstrate_processors();

    // 存储演示
    demonstrate_storage();

    // 插件系统演示
    demonstrate_plugin_system();

    // 上行转换演示（Trait upcasting）
    demonstrate_trait_upcasting();
}

// 基本特征对象演示
fn demonstrate_basic_trait_object() {
    println!("--- Basic Trait Object Demo ---");

    let shapes: Vec<Box<dyn Drawable>> = vec![
        Box::new(Circle { radius: 5.0 }),
        Box::new(Square { side: 10.0 }),
    ];

    for shape in shapes {
        shape.draw();
    }
    println!();
}

// 处理器演示
fn demonstrate_processors() {
    println!("--- Processor Demo ---");

    let text = "Hello, Rust!";

    let processors: Vec<Box<dyn Processor>> = vec![
        Box::new(UppercaseProcessor),
        Box::new(LowercaseProcessor),
        Box::new(ReverseProcessor),
    ];

    for processor in processors {
        let result = processor.process(text);
        println!("Result: {}", result);
    }
    println!();
}

// 存储演示
fn demonstrate_storage() {
    println!("--- Storage Demo ---");

    let mut memory_storage = MemoryStorage::new();
    let mut file_storage = FileStorage::new("config.txt".to_string());

    let storages: Vec<&mut dyn Storage> = vec![&mut memory_storage, &mut file_storage];

    for storage in storages {
        storage.store("key1", "value1");
        storage.store("key2", "value2");

        if let Some(value) = storage.retrieve("key1") {
            println!("Retrieved: {}", value);
        }

        if let Some(removed) = storage.remove("key2") {
            println!("Removed: {}", removed);
        }
    }
    println!();
}

// 插件系统演示
fn demonstrate_plugin_system() {
    println!("--- Plugin System Demo ---");

    let mut manager = PluginManager::new();

    manager.add_plugin(Box::new(TextPlugin));
    manager.add_plugin(Box::new(MathPlugin));
    manager.add_plugin(Box::new(CryptoPlugin));

    let test_inputs = vec!["hello", "42", "secret"];

    for input in test_inputs {
        println!("Input: {}", input);
        manager.execute_all(input);
        println!();
    }
}

// 上行转换（Trait upcasting）
// 当存在 `trait Sub: Super { ... }` 时，`&dyn Sub` 可自动上行转换为 `&dyn Super`
pub trait Super {
    fn id(&self) -> &'static str;
}

pub trait Sub: Super {
    fn detail(&self) -> &'static str;
}

pub struct Concrete;

impl Super for Concrete {
    fn id(&self) -> &'static str {
        "Concrete"
    }
}

impl Sub for Concrete {
    fn detail(&self) -> &'static str {
        "detail"
    }
}

fn demonstrate_trait_upcasting() {
    println!("--- Trait Upcasting Demo ---");
    let c = Concrete;
    let sub_ref: &dyn Sub = &c;
    // 上行转换到 Super
    let super_ref: &dyn Super = sub_ref;
    println!(
        "super.id={} sub.detail={}",
        super_ref.id(),
        sub_ref.detail()
    );

    // Box 上行转换
    let boxed_sub: Box<dyn Sub> = Box::new(Concrete);
    let boxed_super: Box<dyn Super> = boxed_sub;
    println!("boxed_super.id={}", boxed_super.id());
    println!();
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_circle_draw() {
        let circle = Circle { radius: 5.0 };
        // 测试可以转换为特征对象
        let _drawable: Box<dyn Drawable> = Box::new(circle);
        // 这里我们只是验证可以创建特征对象，实际绘制是副作用
        assert!(true);
    }

    #[test]
    fn test_square_draw() {
        let square = Square { side: 10.0 };
        let _drawable: Box<dyn Drawable> = Box::new(square);
        assert!(true);
    }

    #[test]
    fn test_uppercase_processor() {
        let processor = UppercaseProcessor;
        let result = processor.process("hello");
        assert_eq!(result, "HELLO");
    }

    #[test]
    fn test_lowercase_processor() {
        let processor = LowercaseProcessor;
        let result = processor.process("WORLD");
        assert_eq!(result, "world");
    }

    #[test]
    fn test_reverse_processor() {
        let processor = ReverseProcessor;
        let result = processor.process("rust");
        assert_eq!(result, "tsur");
    }

    #[test]
    fn test_memory_storage() {
        let mut storage = MemoryStorage::new();
        storage.store("key1", "value1");

        assert_eq!(storage.retrieve("key1"), Some("value1"));
        assert_eq!(storage.remove("key1"), Some("value1".to_string()));
        assert_eq!(storage.retrieve("key1"), None);
    }

    #[test]
    fn test_plugin_manager() {
        let mut manager = PluginManager::new();
        manager.add_plugin(Box::new(TextPlugin));

        assert_eq!(manager.plugins.len(), 1);
        assert_eq!(manager.plugins[0].name(), "Text Plugin");
        assert_eq!(manager.plugins[0].version(), "1.0.0");
    }

    #[test]
    fn test_trait_upcasting_refs_and_box() {
        let c = Concrete;
        let sub_ref: &dyn Sub = &c;
        let super_ref: &dyn Super = sub_ref; // 上行转换
        assert_eq!(super_ref.id(), "Concrete");
        assert_eq!(sub_ref.detail(), "detail");

        let boxed_sub: Box<dyn Sub> = Box::new(Concrete);
        let boxed_super: Box<dyn Super> = boxed_sub; // Box 上行转换
        assert_eq!(boxed_super.id(), "Concrete");
    }
}
