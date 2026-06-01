//! Dyn Trait Advanced

#![allow(clippy::doc_lazy_continuation)]

//! Dyn Trait 高级用法
//! Dyn Trait
//! - Dyn Upcasting Coercion ( trait 对象向上转换 )
//! - Dyn Upcasting Coercion ( trait to象向onconversion )
//! - Object-Safe 扩展规则
//! - Object-Safe 扩展rule
//! - 自定义接收者类型 (Custom Receiver Types)
//! - and Rust 2024 Edition 协同
//! 注意: 部分特性需要 nightly Rust 或特定版本。
//! : part feature nightly Rust or this 。

use std::{any::Any, fmt::Debug};

// =============================================================================
// 1. Dyn Upcasting Coercion
// =============================================================================

/// 这在 Rust 1.86 (2025) 中已稳定化。
/// in Rust 1.86 (2025) in 。
/// 这in Rust 1.86 (2025) in已稳定化。
/// in Rust 1.86 (2025) in。
/// # 示例场景
/// # examplescenario
/// # example scenario
/// 当你持有一个 `dyn Display + Debug` 对象，但只需要 `dyn Display` 时，
/// when `dyn Display + Debug` to ，but `dyn Display` ，
/// 可以直接进行 trait 对象向上转换，无需重新包装。
/// can trait to on conversion ，。
pub trait Animal: Debug {
    fn speak(&self);
}

pub trait Mammal: Animal {
    fn walk(&self);
}

pub trait Canine: Mammal {
    fn bark(&self);
}

#[derive(Debug)]
pub struct Dog {
    name: String,
}

impl Animal for Dog {
    fn speak(&self) {
        println!("{} says: Hello!", self.name);
    }
}

impl Mammal for Dog {
    fn walk(&self) {
        println!("{} is walking.", self.name);
    }
}

impl Canine for Dog {
    fn bark(&self) {
        println!("{} barks: Woof!", self.name);
    }
}

/// 演示 Dyn Upcasting Coercion
/// Demonstrates Dyn Upcasting Coercion
/// `&dyn Canine` → `&dyn Mammal` → `&dyn Animal` 自动conversion
pub fn demo_dyn_upcasting() {
    println!("=== Dyn Upcasting Coercion 演示 ===");

    let dog = Dog {
        name: String::from("Buddy"),
    };

    // 从最具体的 trait 对象开始
    let canine_ref: &dyn Canine = &dog;

    // 自动 upcast 到 Mammal (无需显式转换)
    let mammal_ref: &dyn Mammal = canine_ref;
    mammal_ref.walk();

    // 自动 upcast 到 Animal
    let animal_ref: &dyn Animal = mammal_ref;
    animal_ref.speak();

    // 也可以一步到位
    let animal_ref2: &dyn Animal = canine_ref;
    println!("{:?}", animal_ref2);

    println!();
}

pub fn feed_animal(animal: &dyn Animal) {
    println!("Feeding: {:?}", animal);
    animal.speak();
}

pub fn demo_upcasting_in_api() {
    println!("=== Upcasting 在 API 中的使用 ===");

    let dog = Dog {
        name: String::from("Rex"),
    };

    // 直接传递 &dyn Canine 到需要 &dyn Animal 的函数
    let canine: &dyn Canine = &dog;
    feed_animal(canine); // 自动 upcast

    println!();
}

// =============================================================================
// 2. Object-Safe 扩展与规则详解
// =============================================================================

/// Object-Safe Trait 判定规则
/// Object-Safe Trait 判定rule
/// 3. 没有静态method（没有 `self` parametermethod）
/// 4. 泛型方法的类型参数必须被具体化（不能保留未绑定的泛型）
/// 4. generic method type parameter must is volume （cannot generic ）
/// ✅ Object-Safe 示例
/// ✅ Object-Safe example
pub trait Drawable: Debug {
    fn draw(&self);
    fn bounds(&self) -> (i32, i32, i32, i32);
}

pub trait Constructor: Sized {
    fn new() -> Self;
    //  ^^^ 返回 Self，要求 Sized，因此不能作为 dyn Constructor
}

pub trait Constructible {
    fn instance_name(&self) -> &str;
}

pub trait NewConstructible: Constructible + Sized {
    fn new(name: String) -> Self;
}

// 现在 Constructible 是 object-safe 的
#[allow(dead_code)]
fn use_constructible(c: &dyn Constructible) {
    println!("Instance: {}", c.instance_name());
}

// =============================================================================
// 3. 自定义接收者类型 (Custom Receiver Types)
// =============================================================================

use std::rc::Rc;
use std::sync::Arc;

pub trait SharedResource: Debug {
    fn shared_operation(self: Rc<Self>);

    fn atomic_operation(self: Arc<Self>);
}

#[derive(Debug)]
pub struct Resource {
    id: u32,
    data: String,
}

impl SharedResource for Resource {
    fn shared_operation(self: Rc<Self>) {
        println!("[Rc] 操作资源 #{}: {}", self.id, self.data);
    }

    fn atomic_operation(self: Arc<Self>) {
        println!("[Arc] 原子操作资源 #{}: {}", self.id, self.data);
    }
}

pub fn demo_custom_receivers() {
    println!("=== 自定义接收者类型演示 ===");

    let res = Rc::new(Resource {
        id: 1,
        data: String::from("shared data"),
    });

    // 克隆 Rc 增加引用计数
    let res2 = Rc::clone(&res);
    println!("Rc 引用计数 (调用前): {}", Rc::strong_count(&res));

    // 使用 Rc<Self> 接收者调用方法 (会消费 Rc)
    res.shared_operation();
    res2.shared_operation();

    // Arc 版本
    let arc_res = Arc::new(Resource {
        id: 2,
        data: String::from("atomic data"),
    });
    arc_res.atomic_operation();

    println!();
}

// =============================================================================
// 4. Dyn Any 与向下转换模式
// =============================================================================

/// `dyn Any` 允许在运行时进行类型识别和向下转换。
/// `dyn Any` in runtime type and under conversion 。
/// 这是实现插件系统、事件总线等模式的基础。
/// system 、line etc. foundation 。
pub trait Plugin: Any + Debug {
    fn name(&self) -> &str;
    fn as_any(&self) -> &dyn Any;
}

#[derive(Debug)]
pub struct LoggerPlugin;

impl Plugin for LoggerPlugin {
    fn name(&self) -> &str {
        "logger"
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

#[derive(Debug)]
pub struct MetricsPlugin {
    counter: u64,
}

impl Plugin for MetricsPlugin {
    fn name(&self) -> &str {
        "metrics"
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

/// 插件管理器
pub struct PluginManager {
    plugins: Vec<Box<dyn Plugin>>,
}

impl Default for PluginManager {
    fn default() -> Self {
        Self::new()
    }
}

impl PluginManager {
    pub fn new() -> Self {
        Self {
            plugins: Vec::new(),
        }
    }

    pub fn register(&mut self, plugin: Box<dyn Plugin>) {
        self.plugins.push(plugin);
    }

    /// 获取特定类型的插件引用
    /// Gets特定类型的插件引用
    /// type reference
    pub fn get_plugin<T: Plugin>(&self) -> Option<&T> {
        self.plugins
            .iter()
            .find_map(|p| p.as_any().downcast_ref::<T>())
    }

    pub fn list_plugins(&self) {
        for p in &self.plugins {
            println!("已加载插件: {}", p.name());
        }
    }
}

pub fn demo_dyn_any() {
    println!("=== Dyn Any 与向下转换演示 ===");

    let mut manager = PluginManager::new();
    manager.register(Box::new(LoggerPlugin));
    manager.register(Box::new(MetricsPlugin { counter: 0 }));

    manager.list_plugins();

    // 向下转换获取具体类型
    if let Some(logger) = manager.get_plugin::<LoggerPlugin>() {
        println!("找到 Logger: {:?}", logger);
    }

    if let Some(metrics) = manager.get_plugin::<MetricsPlugin>() {
        println!("找到 Metrics, counter: {}", metrics.counter);
    }

    println!();
}

// =============================================================================
// 5. Rust 2024 Edition 的 Dyn Trait 改进
// =============================================================================

/// 1. **隐式 `dyn` 弃用**: `Box<Trait>` 语法被移除，必须使用 `Box<dyn Trait>`
/// 1. ** `dyn` **: `Box<Trait>` is ，must `Box<dyn Trait>`
///    (本项目 edition = "2024"，已强制使用显式 dyn)
///    (this project edition = "2024"， dyn)
///    (thisproject edition = "2024"，已强制Use显式 dyn)
/// 2. **`impl Trait` 在更多位置**: 函数指针、关联类型等位置支持 `impl Trait`
/// 2. **`impl Trait` in position **: function pointer 、associated type etc. position `impl Trait`
/// 3. **RPITIT 稳定化**: Return Position Impl Trait In Traits (Rust 1.75+)
/// 4. **Async Fn In Traits 稳定**: 减少手写 `Pin<Box<dyn Future>>`
pub trait Processor {
    type Input;
    type Output: Debug;

    fn process(&self, input: Self::Input) -> Self::Output;
}

/// 使用 trait 对象实现动态分发
/// trait to
/// Use trait to象Implementation ofdynamic dispatch
pub struct DynamicPipeline {
    processors: Vec<Box<dyn DynProcessor>>,
}

/// Object-safe 版this Processor trait
pub trait DynProcessor: Debug {
    fn process_dyn(&self, input: &dyn Any) -> Box<dyn Any>;
    fn type_name(&self) -> &'static str;
}

impl Default for DynamicPipeline {
    fn default() -> Self {
        Self::new()
    }
}

impl DynamicPipeline {
    pub fn new() -> Self {
        Self {
            processors: Vec::new(),
        }
    }

    pub fn add(&mut self, processor: Box<dyn DynProcessor>) {
        self.processors.push(processor);
    }

    pub fn run(&self, input: &dyn Any) {
        let mut current: &dyn Any = input;
        for (i, proc) in self.processors.iter().enumerate() {
            println!("阶段 {}: 使用 {}", i, proc.type_name());
            let output = proc.process_dyn(current);
            // 注意: 这里为了演示简化，实际应用需要更严谨的类型处理
            current = Box::leak(output); // ⚠️ 仅演示，生产代码不应如此
        }
    }
}

// =============================================================================
// 6. 实用工具函数
// =============================================================================

pub fn same_object<T: ?Sized>(a: &T, b: &T) -> bool {
    std::ptr::eq(a as *const T as *const (), b as *const T as *const ())
}

/// 安全的向下转换包装
/// under conversion
pub fn try_downcast_ref<T: Any>(obj: &dyn Any) -> Option<&T> {
    obj.downcast_ref::<T>()
}

// =============================================================================
// 7. 运行所有演示
// =============================================================================

pub fn run_dyn_trait_advanced_examples() {
    println!("╔═══════════════════════════════════════════════════════════════╗");
    println!("║            Dyn Trait 高级用法综合演示                         ║");
    println!("╚═══════════════════════════════════════════════════════════════╝");
    println!();

    demo_dyn_upcasting();
    demo_upcasting_in_api();
    demo_custom_receivers();
    demo_dyn_any();

    println!("✅ Dyn Trait 高级用法演示完成");
    println!();
    println!("💡 要点总结:");
    println!("   • Dyn Upcasting: trait 对象自动向上转换 (Rust 1.86+ 稳定)");
    println!("   • Object-Safe: 注意 Self: Sized 会阻止 dyn Trait");
    println!("   • 自定义接收者: Rc<Self> / Arc<Self> 支持特殊场景");
    println!("   • Dyn Any: 运行时类型识别的基础");
    println!("   • Rust 2024: 强制显式 dyn，代码更清晰");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dyn_upcasting() {
        let dog = Dog {
            name: String::from("TestDog"),
        };
        let canine: &dyn Canine = &dog;
        let _animal: &dyn Animal = canine; // upcast
        // 如果能编译，说明 upcasting 工作正常
    }

    #[test]
    fn test_plugin_downcast() {
        let plugin: Box<dyn Plugin> = Box::new(MetricsPlugin { counter: 42 });
        let any = plugin.as_any();
        let metrics = any.downcast_ref::<MetricsPlugin>().unwrap();
        assert_eq!(metrics.counter, 42);
    }

    #[test]
    fn test_same_object() {
        let dog = Dog {
            name: String::from("Same"),
        };
        let r1: &dyn Animal = &dog;
        let r2: &dyn Animal = &dog;
        assert!(same_object(r1, r2));
    }

    #[test]
    fn test_custom_receiver_rc() {
        let res = Rc::new(Resource {
            id: 99,
            data: String::from("test"),
        });
        res.shared_operation();
        // 测试通过即说明 Rc<Self> 接收者工作正常
    }
}
