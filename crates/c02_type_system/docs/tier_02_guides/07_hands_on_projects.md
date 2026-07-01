# 🎯 C02: Type System - 实战项目集

> **创建日期**: 2025-10-25
> **文档版本**: v1.0
> **适用模块**: C02 类型系统
> **目标**: 通过实战项目深入理解 Rust 的类型系统和 Trait

---

## 📐 知识结构

### 概念定义

**实战项目集 (Practical Projects Collection)**:

- **定义**: 收集和组织的实战项目集合，用于演示类型系统的实际应用
- **类型**: 项目集合文档
- **范畴**: 类型系统、项目实践
- **版本**: Rust 1.0+
- **相关概念**: 类型系统、Trait、多态、项目实践

### 属性特征

**核心属性**:

- **层次性**: 从简单到复杂的项目
- **实用性**: 解决实际问题
- **完整性**: 每个项目都有完整实现
- **可运行性**: 所有项目都可以运行

### 关系连接

**组合关系**:

- 实战项目集 --[contains]--> 多个实战项目
- 学习路径 --[uses]--> 实战项目集

**依赖关系**:

- 实战项目集 --[depends-on]--> 类型系统知识
- 项目实践 --[depends-on]--> 实战项目集

### 思维导图

```text
实战项目集
│
├── 简单 Trait 系统
│   └── Trait 定义
├── 多态设计实践
│   └── Trait 对象
└── 自定义 Iterator
    └── 关联类型
```

---

## 📋 项目概览

本文档提供了 **3个精心设计的实战项目**，帮助你掌握 Rust 类型系统的核心概念。

| #   | 项目名称  | 难度   | 预计时间 | 核心概念 |
| :--- | :--- | :--- | :--- | :--- |
| 1   | [简单 Trait 系统](#项目1-简单-trait-系统) | ⭐     | 1-2小时  | Trait 定义、实现     |
| 2   | [多态设计实践](#项目2-多态设计实践)       | ⭐⭐   | 2-3小时  | Trait 对象、动态分派 |
| 3   | [自定义 Iterator](#项目3-自定义-iterator) | ⭐⭐⭐ | 3-4小时  | 关联类型、高级 Trait |

---

## 项目1: 简单 Trait 系统

### 📖 项目说明

**难度**: ⭐
**预计时间**: 1-2小时
**目标**: 理解 Trait 定义和实现

### 学习目标

1. 定义自己的 Trait
2. 为不同类型实现 Trait
3. 使用 Trait Bounds
4. 理解派生 Trait

### 功能需求

#### 基础功能

1. 定义 `Drawable` trait
2. 为不同图形实现 trait
3. 实现泛型函数使用 trait
4. 使用派生 trait

### 项目结构

```text
shape_system/
├── Cargo.toml
└── src/
    ├── main.rs
    └── shapes.rs
```

### 核心代码实现

#### `shapes.rs`

```rust
use std::f64::consts::PI;

/// Drawable trait - 所有可绘制对象必须实现
pub trait Drawable {
    /// 绘制对象
    fn draw(&self);

    /// 获取描述
    fn description(&self) -> String;

    /// 默认实现：显示对象信息
    fn show_info(&self) {
        println!("=== {} ===", self.description());
        self.draw();
        println!();
    }
}

/// Shape trait - 几何形状特性
pub trait Shape: Drawable {
    /// 计算面积
    fn area(&self) -> f64;

    /// 计算周长
    fn perimeter(&self) -> f64;
}

/// 圆形
#[derive(Debug, Clone)]
pub struct Circle {
    pub radius: f64,
}

impl Circle {
    pub fn new(radius: f64) -> Self {
        Circle { radius }
    }
}

impl Drawable for Circle {
    fn draw(&self) {
        println!("  ⭕ 圆形");
        println!("     半径: {:.2}", self.radius);
    }

    fn description(&self) -> String {
        format!("Circle(r={})", self.radius)
    }
}

impl Shape for Circle {
    fn area(&self) -> f64 {
        PI * self.radius * self.radius
    }

    fn perimeter(&self) -> f64 {
        2.0 * PI * self.radius
    }
}

/// 矩形
#[derive(Debug, Clone)]
pub struct Rectangle {
    pub width: f64,
    pub height: f64,
}

impl Rectangle {
    pub fn new(width: f64, height: f64) -> Self {
        Rectangle { width, height }
    }
}

impl Drawable for Rectangle {
    fn draw(&self) {
        println!("  ▭ 矩形");
        println!("     宽度: {:.2}, 高度: {:.2}", self.width, self.height);
    }

    fn description(&self) -> String {
        format!("Rectangle({}x{})", self.width, self.height)
    }
}

impl Shape for Rectangle {
    fn area(&self) -> f64 {
        self.width * self.height
    }

    fn perimeter(&self) -> f64 {
        2.0 * (self.width + self.height)
    }
}

/// 三角形
#[derive(Debug, Clone)]
pub struct Triangle {
    pub base: f64,
    pub height: f64,
    pub side1: f64,
    pub side2: f64,
}

impl Triangle {
    pub fn new(base: f64, height: f64, side1: f64, side2: f64) -> Self {
        Triangle { base, height, side1, side2 }
    }
}

impl Drawable for Triangle {
    fn draw(&self) {
        println!("  🔺 三角形");
        println!("     底边: {:.2}, 高: {:.2}", self.base, self.height);
    }

    fn description(&self) -> String {
        format!("Triangle(base={})", self.base)
    }
}

impl Shape for Triangle {
    fn area(&self) -> f64 {
        0.5 * self.base * self.height
    }

    fn perimeter(&self) -> f64 {
        self.base + self.side1 + self.side2
    }
}

/// 使用 trait bound 的泛型函数
pub fn print_shape_info<T: Shape>(shape: &T) {
    println!("📏 形状信息:");
    shape.draw();
    println!("   面积: {:.2}", shape.area());
    println!("   周长: {:.2}", shape.perimeter());
}

/// 比较两个形状的面积
pub fn compare_area<T: Shape, U: Shape>(shape1: &T, shape2: &U) {
    let area1 = shape1.area();
    let area2 = shape2.area();

    println!("📊 面积比较:");
    println!("   {} 面积: {:.2}", shape1.description(), area1);
    println!("   {} 面积: {:.2}", shape2.description(), area2);

    if area1 > area2 {
        println!("   ✅ {} 面积更大", shape1.description());
    } else if area1 < area2 {
        println!("   ✅ {} 面积更大", shape2.description());
    } else {
        println!("   ✅ 面积相等");
    }
}

/// 找出面积最大的形状
pub fn find_largest<T: Shape>(shapes: &[T]) -> Option<&T> {
    shapes.iter().max_by(|a, b| {
        a.area().partial_cmp(&b.area()).unwrap()
    })
}
```

#### `main.rs`

```rust
mod shapes;
use shapes::*;

fn main() {
    println!("===== 简单 Trait 系统测试 =====\n");

    // 测试1: 基础 trait 实现
    {
        println!("测试1: 基础 Trait 实现\n");

        let circle = Circle::new(5.0);
        let rectangle = Rectangle::new(4.0, 6.0);
        let triangle = Triangle::new(3.0, 4.0, 3.0, 5.0);

        circle.show_info();
        rectangle.show_info();
        triangle.show_info();
    }

    // 测试2: Shape trait
    {
        println!("测试2: Shape Trait\n");

        let circle = Circle::new(3.0);
        print_shape_info(&circle);

        println!();

        let rect = Rectangle::new(5.0, 10.0);
        print_shape_info(&rect);
        println!();
    }

    // 测试3: 比较形状
    {
        println!("测试3: 形状比较\n");

        let circle = Circle::new(5.0);
        let rectangle = Rectangle::new(7.0, 7.0);

        compare_area(&circle, &rectangle);
        println!();
    }

    // 测试4: 找出最大形状
    {
        println!("测试4: 找出最大形状\n");

        let shapes = vec![
            Circle::new(3.0),
            Circle::new(5.0),
            Circle::new(2.0),
        ];

        if let Some(largest) = find_largest(&shapes) {
            println!("最大的圆形:");
            largest.show_info();
            println!("面积: {:.2}", largest.area());
        }
    }

    // 测试5: 泛型集合
    {
        println!("\n测试5: 泛型集合\n");

        fn total_area<T: Shape>(shapes: &[T]) -> f64 {
            shapes.iter().map(|s| s.area()).sum()
        }

        let circles = vec![
            Circle::new(1.0),
            Circle::new(2.0),
            Circle::new(3.0),
        ];

        let rectangles = vec![
            Rectangle::new(2.0, 3.0),
            Rectangle::new(4.0, 5.0),
        ];

        println!("圆形总面积: {:.2}", total_area(&circles));
        println!("矩形总面积: {:.2}", total_area(&rectangles));
    }
}
```

### 测试方式

```bash
cargo new shape_system
cd shape_system
# 复制上述代码
cargo run
```

### 预期输出

```text
===== 简单 Trait 系统测试 =====

测试1: 基础 Trait 实现

=== Circle(r=5) ===
  ⭕ 圆形
     半径: 5.00

=== Rectangle(4x6) ===
  ▭ 矩形
     宽度: 4.00, 高度: 6.00

=== Triangle(base=3) ===
  🔺 三角形
     底边: 3.00, 高: 4.00

测试2: Shape Trait

📏 形状信息:
  ⭕ 圆形
     半径: 3.00
   面积: 28.27
   周长: 18.85

📏 形状信息:
  ▭ 矩形
     宽度: 5.00, 高度: 10.00
   面积: 50.00
   周长: 30.00

测试3: 形状比较

📊 面积比较:
   Circle(r=5) 面积: 78.54
   Rectangle(7x7) 面积: 49.00
   ✅ Circle(r=5) 面积更大

测试4: 找出最大形状

最大的圆形:
=== Circle(r=5) ===
  ⭕ 圆形
     半径: 5.00

面积: 78.54

测试5: 泛型集合

圆形总面积: 43.98
矩形总面积: 26.00
```

### 关键知识点

1. **Trait 定义**: 定义共享行为
2. **Trait 实现**: 为类型实现 trait
3. **Supertrait**: `Shape: Drawable` 继承关系
4. **默认实现**: `show_info` 有默认行为
5. **Trait Bounds**: 泛型函数约束

### 扩展方向

1. 添加更多图形（椭圆、多边形）
2. 实现 `PartialEq` 和 `Ord` trait
3. 添加颜色和样式支持
4. 实现图形变换（旋转、缩放）

---

## 项目2: 多态设计实践

### 📖 项目说明2

**难度**: ⭐⭐
**预计时间**: 2-3小时
**目标**: 掌握 Trait 对象和动态分派

### 学习目标2

1. 使用 `dyn Trait` 实现多态
2. 理解静态分派 vs 动态分派
3. 实现插件系统
4. 使用 `Box<dyn Trait>`

### 功能需求2

#### 基础功能2

1. 定义插件系统接口
2. 实现不同类型的插件
3. 动态加载和执行插件
4. 插件管理器

### 项目结构2

```text
plugin_system/
├── Cargo.toml
└── src/
    ├── main.rs
    ├── plugin.rs
    └── plugins/
        ├── mod.rs
        ├── logger.rs
        ├── validator.rs
        └── transformer.rs
```

### 核心代码实现2

#### `plugin.rs`

```rust
use std::any::Any;

/// 插件 trait - 所有插件必须实现
pub trait Plugin: Any {
    /// 插件名称
    fn name(&self) -> &str;

    /// 插件版本
    fn version(&self) -> &str {
        "1.0.0"
    }

    /// 插件描述
    fn description(&self) -> &str;

    /// 初始化插件
    fn initialize(&mut self) {
        println!("🔌 插件 '{}' 初始化", self.name());
    }

    /// 执行插件
    fn execute(&self, input: &str) -> Result<String, String>;

    /// 关闭插件
    fn shutdown(&mut self) {
        println!("🔌 插件 '{}' 关闭", self.name());
    }

    /// 转换为 Any，用于向下转型
    fn as_any(&self) -> &dyn Any;
}

/// 插件管理器
pub struct PluginManager {
    plugins: Vec<Box<dyn Plugin>>,
}

impl PluginManager {
    pub fn new() -> Self {
        PluginManager {
            plugins: Vec::new(),
        }
    }

    /// 注册插件
    pub fn register(&mut self, mut plugin: Box<dyn Plugin>) {
        println!("📦 注册插件: {} v{}", plugin.name(), plugin.version());
        plugin.initialize();
        self.plugins.push(plugin);
    }

    /// 列出所有插件
    pub fn list_plugins(&self) {
        println!("\n📋 已注册的插件:");
        for (i, plugin) in self.plugins.iter().enumerate() {
            println!("  {}. {} v{} - {}",
                     i + 1,
                     plugin.name(),
                     plugin.version(),
                     plugin.description());
        }
    }

    /// 执行插件
    pub fn execute(&self, plugin_name: &str, input: &str) -> Result<String, String> {
        for plugin in &self.plugins {
            if plugin.name() == plugin_name {
                return plugin.execute(input);
            }
        }
        Err(format!("插件 '{}' 未找到", plugin_name))
    }

    /// 执行所有插件（pipeline）
    pub fn execute_all(&self, input: &str) -> Result<String, String> {
        let mut result = input.to_string();

        for plugin in &self.plugins {
            println!("  🔄 执行: {}", plugin.name());
            result = plugin.execute(&result)?;
        }

        Ok(result)
    }

    /// 获取插件数量
    pub fn count(&self) -> usize {
        self.plugins.len()
    }
}

impl Drop for PluginManager {
    fn drop(&mut self) {
        println!("\n🔌 关闭所有插件...");
        for plugin in &mut self.plugins {
            plugin.shutdown();
        }
    }
}
```

#### `plugins/logger.rs`

```rust
use crate::plugin::Plugin;
use std::any::Any;

/// 日志插件 - 记录所有输入
pub struct LoggerPlugin {
    name: String,
    log_count: usize,
}

impl LoggerPlugin {
    pub fn new() -> Self {
        LoggerPlugin {
            name: "Logger".to_string(),
            log_count: 0,
        }
    }
}

impl Plugin for LoggerPlugin {
    fn name(&self) -> &str {
        &self.name
    }

    fn description(&self) -> &str {
        "记录所有输入内容"
    }

    fn execute(&self, input: &str) -> Result<String, String> {
        println!("    📝 [Logger] 输入: {}", input);
        Ok(input.to_string())
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
```

#### `plugins/validator.rs`

```rust
use crate::plugin::Plugin;
use std::any::Any;

/// 验证插件 - 验证输入有效性
pub struct ValidatorPlugin {
    min_length: usize,
}

impl ValidatorPlugin {
    pub fn new(min_length: usize) -> Self {
        ValidatorPlugin { min_length }
    }
}

impl Plugin for ValidatorPlugin {
    fn name(&self) -> &str {
        "Validator"
    }

    fn description(&self) -> &str {
        "验证输入长度"
    }

    fn execute(&self, input: &str) -> Result<String, String> {
        if input.len() < self.min_length {
            Err(format!("输入太短: {} < {}", input.len(), self.min_length))
        } else {
            println!("    ✅ [Validator] 验证通过 (长度: {})", input.len());
            Ok(input.to_string())
        }
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
```

#### `plugins/transformer.rs`

```rust
use crate::plugin::Plugin;
use std::any::Any;

/// 转换插件 - 转换输入内容
pub struct TransformerPlugin {
    mode: TransformMode,
}

pub enum TransformMode {
    Uppercase,
    Lowercase,
    Reverse,
}

impl TransformerPlugin {
    pub fn new(mode: TransformMode) -> Self {
        TransformerPlugin { mode }
    }
}

impl Plugin for TransformerPlugin {
    fn name(&self) -> &str {
        "Transformer"
    }

    fn description(&self) -> &str {
        "转换输入内容"
    }

    fn execute(&self, input: &str) -> Result<String, String> {
        let result = match self.mode {
            TransformMode::Uppercase => input.to_uppercase(),
            TransformMode::Lowercase => input.to_lowercase(),
            TransformMode::Reverse => input.chars().rev().collect(),
        };

        println!("    🔄 [Transformer] 转换完成");
        Ok(result)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}
```

#### `plugins/mod.rs`

```rust
pub mod logger;
pub mod validator;
pub mod transformer;
```

#### `main.rs`2

```rust
mod plugin;
mod plugins;

use plugin::*;
use plugins::logger::LoggerPlugin;
use plugins::validator::ValidatorPlugin;
use plugins::transformer::{TransformerPlugin, TransformMode};

fn main() {
    println!("===== 多态插件系统测试 =====\n");

    // 测试1: 基础插件注册
    {
        println!("测试1: 基础插件注册\n");

        let mut manager = PluginManager::new();

        manager.register(Box::new(LoggerPlugin::new()));
        manager.register(Box::new(ValidatorPlugin::new(3)));

        manager.list_plugins();
        println!();
    }

    // 测试2: 执行单个插件
    {
        println!("\n测试2: 执行单个插件\n");

        let mut manager = PluginManager::new();
        manager.register(Box::new(LoggerPlugin::new()));
        manager.register(Box::new(ValidatorPlugin::new(5)));

        let result = manager.execute("Logger", "Hello, Rust!");
        println!("结果: {:?}\n", result);

        let result2 = manager.execute("Validator", "Hi");
        println!("结果: {:?}", result2);
    }

    // 测试3: Pipeline 执行
    {
        println!("\n\n测试3: Pipeline 执行\n");

        let mut manager = PluginManager::new();
        manager.register(Box::new(LoggerPlugin::new()));
        manager.register(Box::new(ValidatorPlugin::new(3)));
        manager.register(Box::new(TransformerPlugin::new(TransformMode::Uppercase)));

        println!("执行 Pipeline:");
        match manager.execute_all("hello rust") {
            Ok(result) => println!("\n✅ 最终结果: {}", result),
            Err(e) => println!("\n❌ 错误: {}", e),
        }
    }

    // 测试4: 不同转换模式
    {
        println!("\n\n测试4: 不同转换模式\n");

        let transformers: Vec<Box<dyn Plugin>> = vec![
            Box::new(TransformerPlugin::new(TransformMode::Uppercase)),
            Box::new(TransformerPlugin::new(TransformMode::Lowercase)),
            Box::new(TransformerPlugin::new(TransformMode::Reverse)),
        ];

        let input = "Hello World";
        println!("原始输入: {}\n", input);

        for transformer in transformers {
            match transformer.execute(input) {
                Ok(result) => println!("  结果: {}", result),
                Err(e) => println!("  错误: {}", e),
            }
        }
    }

    // 测试5: 错误处理
    {
        println!("\n\n测试5: 错误处理\n");

        let mut manager = PluginManager::new();
        manager.register(Box::new(ValidatorPlugin::new(10)));

        let inputs = vec!["Hi", "Hello", "Hello, World!"];

        for input in inputs {
            println!("输入: '{}'", input);
            match manager.execute("Validator", input) {
                Ok(_) => println!("  ✅ 通过\n"),
                Err(e) => println!("  ❌ {}\n", e),
            }
        }
    }
}
```

### 测试方式2

```bash
cargo new plugin_system
cd plugin_system
# 复制上述代码
cargo run
```

### 预期输出2

```text
===== 多态插件系统测试 =====

测试1: 基础插件注册

📦 注册插件: Logger v1.0.0
🔌 插件 'Logger' 初始化
📦 注册插件: Validator v1.0.0
🔌 插件 'Validator' 初始化

📋 已注册的插件:
  1. Logger v1.0.0 - 记录所有输入内容
  2. Validator v1.0.0 - 验证输入长度

🔌 关闭所有插件...
🔌 插件 'Logger' 关闭
🔌 插件 'Validator' 关闭


测试2: 执行单个插件

📦 注册插件: Logger v1.0.0
🔌 插件 'Logger' 初始化
📦 注册插件: Validator v1.0.0
🔌 插件 'Validator' 初始化
    📝 [Logger] 输入: Hello, Rust!
结果: Ok("Hello, Rust!")

结果: Err("输入太短: 2 < 5")
...
```

### 关键知识点2

1. **Trait 对象**: `Box<dyn Plugin>` 实现多态
2. **动态分派**: 运行时确定调用哪个方法
3. **Any trait**: 支持向下转型
4. **插件架构**: 可扩展的系统设计
5. **错误处理**: 使用 `Result` 传播错误

### 扩展方向2

1. 添加插件配置支持
2. 实现插件依赖管理
3. 添加异步插件支持
4. 实现插件热加载

---

## 项目3: 自定义 Iterator

### 📖 项目说明3

**难度**: ⭐⭐⭐
**预计时间**: 3-4小时
**目标**: 掌握关联类型和高级 Trait

### 学习目标3

1. 实现自定义迭代器
2. 理解关联类型
3. 使用迭代器适配器
4. 实现链式调用

### 功能需求3

#### 基础功能3

1. 实现 `Iterator` trait
2. 实现范围迭代器
3. 实现步长迭代器
4. 实现过滤迭代器

#### 进阶功能

1. 实现迭代器组合
2. 实现无限迭代器
3. 实现自定义适配器

### 核心代码

由于篇幅限制，这里提供核心结构和示例：

```rust
/// 自定义范围迭代器
struct RangeIterator {
    current: i32,
    end: i32,
    step: i32,
}

impl Iterator for RangeIterator {
    type Item = i32;  // 关联类型

    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.end {
            let value = self.current;
            self.current += self.step;
            Some(value)
        } else {
            None
        }
    }
}

/// 斐波那契数列迭代器
struct Fibonacci {
    current: u64,
    next: u64,
}

impl Iterator for Fibonacci {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let new_next = self.current + self.next;
        self.current = self.next;
        self.next = new_next;
        Some(self.current)
    }
}
```

_完整代码请参考项目文件_-

### 关键知识点3

1. **关联类型**: `type Item = T`
2. **Iterator trait**: 实现迭代行为
3. **链式调用**: `.map().filter().collect()`
4. **惰性求值**: 迭代器只在需要时计算
5. **适配器模式**: 组合不同的迭代器

---

## 📝 总结

### 项目进阶路径

1. **项目1**: 基础 Trait → 理解接口定义
2. **项目2**: Trait 对象 → 理解多态和动态分派
3. **项目3**: 高级 Trait → 理解关联类型和泛型

### 核心概念总结

| 概念         | 项目1  | 项目2  | 项目3  |
| :--- | :--- | :--- | :--- || Trait 定义   | ✅✅✅ | ✅✅   | ✅✅   |
| Trait 实现   | ✅✅✅ | ✅✅   | ✅✅✅ |
| Trait Bounds | ✅✅   | ✅     | ✅✅   |
| Trait 对象   | ❌     | ✅✅✅ | ✅     |
| 关联类型     | ❌     | ❌     | ✅✅✅ |

### 相关文档

- 📖 [代码示例集合](06_code_examples.md)
- 📖 [Trait 基础](../tier_01_foundations/05_Trait基础.md)
- 📖 [泛型与多态](02_泛型与多态.md)

---

**文档版本**: v1.0
**创建日期**: 2025-10-25
**维护状态**: 活跃维护

**🎯 通过实战项目，掌握 Rust 强大的类型系统！🦀**-
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
