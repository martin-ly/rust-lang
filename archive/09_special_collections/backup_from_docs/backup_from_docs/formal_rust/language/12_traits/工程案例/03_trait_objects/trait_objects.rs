//! 特质对象案例
//! 
//! 本模块演示特质对象的使用，包括对象安全、动态分发、虚函数表等概念。
//! 
//! 理论映射：
//! - 特质对象: Box<dyn T> → O = (T, v, d)
//! - 对象安全: ObjectSafe(T) → ∀m ∈ M(T). ObjectSafe(m)
//! - 动态分发: 运行时确定具体类型

use std::fmt::{Display, Debug};

/// 对象安全的特质
/// 
/// 理论映射：ObjectSafe(T) → ∀m ∈ M(T). ObjectSafe(m)
/// 条件：
/// 1. 方法不能有泛型参数
/// 2. 方法不能返回Self
/// 3. 方法不能有where子句
pub trait Drawable {
    /// 绘制方法 - 对象安全
    fn draw(&self);
    
    /// 获取信息 - 对象安全
    fn get_info(&self) -> String;
    
    /// 获取类型名称 - 对象安全
    fn type_name(&self) -> &'static str;
}

/// 圆形类型
pub struct Circle {
    radius: f64,
    center: (f64, f64),
}

impl Drawable for Circle {
    fn draw(&self) {
        println!("Drawing circle with radius {} at ({}, {})", 
                 self.radius, self.center.0, self.center.1);
    }
    
    fn get_info(&self) -> String {
        format!("Circle: radius={}, center=({}, {})", 
                self.radius, self.center.0, self.center.1)
    }
    
    fn type_name(&self) -> &'static str {
        "Circle"
    }
}

/// 矩形类型
pub struct Rectangle {
    width: f64,
    height: f64,
    position: (f64, f64),
}

impl Drawable for Rectangle {
    fn draw(&self) {
        println!("Drawing rectangle {}x{} at ({}, {})", 
                 self.width, self.height, self.position.0, self.position.1);
    }
    
    fn get_info(&self) -> String {
        format!("Rectangle: {}x{}, position=({}, {})", 
                self.width, self.height, self.position.0, self.position.1)
    }
    
    fn type_name(&self) -> &'static str {
        "Rectangle"
    }
}

/// 三角形类型
pub struct Triangle {
    points: [(f64, f64); 3],
}

impl Drawable for Triangle {
    fn draw(&self) {
        println!("Drawing triangle with points: ({}, {}), ({}, {}), ({}, {})", 
                 self.points[0].0, self.points[0].1,
                 self.points[1].0, self.points[1].1,
                 self.points[2].0, self.points[2].1);
    }
    
    fn get_info(&self) -> String {
        format!("Triangle: points=({}, {}), ({}, {}), ({}, {})", 
                self.points[0].0, self.points[0].1,
                self.points[1].0, self.points[1].1,
                self.points[2].0, self.points[2].1)
    }
    
    fn type_name(&self) -> &'static str {
        "Triangle"
    }
}

/// 特质对象集合
/// 
/// 理论映射：O = (T, v, d)
/// - T: Drawable
/// - v: 虚函数表
/// - d: 数据指针
pub struct DrawingCanvas {
    shapes: Vec<Box<dyn Drawable>>,
}

impl DrawingCanvas {
    pub fn new() -> Self {
        Self { shapes: Vec::new() }
    }
    
    /// 添加形状
    pub fn add_shape(&mut self, shape: Box<dyn Drawable>) {
        self.shapes.push(shape);
    }
    
    /// 绘制所有形状
    pub fn draw_all(&self) {
        println!("Drawing canvas with {} shapes:", self.shapes.len());
        for (i, shape) in self.shapes.iter().enumerate() {
            println!("Shape {} ({}):", i, shape.type_name());
            shape.draw();
            println!("Info: {}", shape.get_info());
        }
    }
    
    /// 获取形状信息
    pub fn get_shape_info(&self, index: usize) -> Option<String> {
        self.shapes.get(index).map(|shape| shape.get_info())
    }
}

/// 非对象安全的特质示例
/// 
/// 这个特质不满足对象安全条件
pub trait NonObjectSafe {
    /// 返回Self - 违反对象安全
    fn clone_self(&self) -> Self;
    
    /// 泛型方法 - 违反对象安全
    fn generic_method<T>(&self, _item: T);
    
    /// where子句 - 违反对象安全
    fn where_method(&self) 
    where 
        Self: Display,
    {
        println!("Display: {}", self);
    }
}

/// 对象安全的特质变体
/// 
/// 通过关联类型实现类似功能
pub trait ObjectSafeClone {
    type Output;
    fn clone_self(&self) -> Self::Output;
}

/// 动态分发性能测试
/// 
/// 理论映射：动态分发 vs 静态分发
pub trait Processor {
    fn process(&self) -> i32;
}

pub struct FastProcessor;
pub struct SlowProcessor;

impl Processor for FastProcessor {
    fn process(&self) -> i32 {
        42 // 快速处理
    }
}

impl Processor for SlowProcessor {
    fn process(&self) -> i32 {
        // 模拟慢速处理
        std::thread::sleep(std::time::Duration::from_millis(1));
        42
    }
}

/// 特质对象的生命周期管理
/// 
/// 理论映射：生命周期在特质对象中的应用
pub trait LifecycleManager {
    fn get_name(&self) -> &str;
    fn is_alive(&self) -> bool;
}

pub struct ManagedObject {
    name: String,
    alive: bool,
}

impl LifecycleManager for ManagedObject {
    fn get_name(&self) -> &str {
        &self.name
    }
    
    fn is_alive(&self) -> bool {
        self.alive
    }
}

/// 特质对象的错误处理
/// 
/// 理论映射：特质对象在错误处理中的应用
pub trait ErrorHandler {
    fn handle_error(&self, error: &str) -> Result<(), String>;
    fn can_handle(&self, error_type: &str) -> bool;
}

pub struct ConsoleErrorHandler;
pub struct FileErrorHandler {
    file_path: String,
}

impl ErrorHandler for ConsoleErrorHandler {
    fn handle_error(&self, error: &str) -> Result<(), String> {
        println!("Console error handler: {}", error);
        Ok(())
    }
    
    fn can_handle(&self, _error_type: &str) -> bool {
        true // 可以处理所有错误
    }
}

impl ErrorHandler for FileErrorHandler {
    fn handle_error(&self, error: &str) -> Result<(), String> {
        println!("File error handler ({}): {}", self.file_path, error);
        Ok(())
    }
    
    fn can_handle(&self, error_type: &str) -> bool {
        error_type.contains("file") // 只处理文件相关错误
    }
}

/// 特质对象的序列化
/// 
/// 理论映射：特质对象在序列化中的应用
pub trait Serializable {
    fn serialize(&self) -> String;
    fn deserialize(data: &str) -> Result<Box<dyn Serializable>, String>;
}

impl Serializable for Circle {
    fn serialize(&self) -> String {
        format!("Circle:{}:{}:{}", self.radius, self.center.0, self.center.1)
    }
    
    fn deserialize(data: &str) -> Result<Box<dyn Serializable>, String> {
        let parts: Vec<&str> = data.split(':').collect();
        if parts.len() == 4 && parts[0] == "Circle" {
            let radius: f64 = parts[1].parse().map_err(|_| "Invalid radius")?;
            let x: f64 = parts[2].parse().map_err(|_| "Invalid x")?;
            let y: f64 = parts[3].parse().map_err(|_| "Invalid y")?;
            Ok(Box::new(Circle { radius, center: (x, y) }))
        } else {
            Err("Invalid Circle data".to_string())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 测试特质对象创建
    #[test]
    fn test_trait_object_creation() {
        let circle = Circle { radius: 5.0, center: (0.0, 0.0) };
        let rectangle = Rectangle { width: 10.0, height: 5.0, position: (1.0, 1.0) };
        
        let shapes: Vec<Box<dyn Drawable>> = vec![
            Box::new(circle),
            Box::new(rectangle),
        ];
        
        assert_eq!(shapes.len(), 2);
    }

    /// 测试动态分发
    #[test]
    fn test_dynamic_dispatch() {
        let mut canvas = DrawingCanvas::new();
        
        canvas.add_shape(Box::new(Circle { radius: 3.0, center: (0.0, 0.0) }));
        canvas.add_shape(Box::new(Rectangle { width: 4.0, height: 6.0, position: (1.0, 1.0) }));
        canvas.add_shape(Box::new(Triangle { points: [(0.0, 0.0), (1.0, 0.0), (0.5, 1.0)] }));
        
        canvas.draw_all();
        
        assert_eq!(canvas.shapes.len(), 3);
    }

    /// 测试对象安全
    #[test]
    fn test_object_safety() {
        // 这些特质对象应该可以正常创建
        let _circle: Box<dyn Drawable> = Box::new(Circle { radius: 1.0, center: (0.0, 0.0) });
        let _rectangle: Box<dyn Drawable> = Box::new(Rectangle { width: 1.0, height: 1.0, position: (0.0, 0.0) });
        
        // 验证特质对象可以调用方法
        let shape: Box<dyn Drawable> = Box::new(Circle { radius: 2.0, center: (0.0, 0.0) });
        assert_eq!(shape.type_name(), "Circle");
    }

    /// 测试生命周期管理
    #[test]
    fn test_lifecycle_management() {
        let objects: Vec<Box<dyn LifecycleManager>> = vec![
            Box::new(ManagedObject { name: "Object1".to_string(), alive: true }),
            Box::new(ManagedObject { name: "Object2".to_string(), alive: false }),
        ];
        
        for obj in &objects {
            println!("Object: {}, Alive: {}", obj.get_name(), obj.is_alive());
        }
    }

    /// 测试错误处理
    #[test]
    fn test_error_handling() {
        let handlers: Vec<Box<dyn ErrorHandler>> = vec![
            Box::new(ConsoleErrorHandler),
            Box::new(FileErrorHandler { file_path: "/tmp/errors.log".to_string() }),
        ];
        
        for handler in &handlers {
            let _ = handler.handle_error("Test error");
        }
    }

    /// 测试序列化
    #[test]
    fn test_serialization() {
        let circle = Circle { radius: 5.0, center: (1.0, 2.0) };
        let serialized = circle.serialize();
        
        let deserialized = Serializable::deserialize(&serialized);
        assert!(deserialized.is_ok());
    }

    /// 测试性能比较
    #[test]
    fn test_performance_comparison() {
        let processors: Vec<Box<dyn Processor>> = vec![
            Box::new(FastProcessor),
            Box::new(SlowProcessor),
        ];
        
        for processor in &processors {
            let result = processor.process();
            assert_eq!(result, 42);
        }
    }
}

/// 示例用法
pub fn run_examples() {
    println!("=== 特质对象案例 ===");
    
    // 创建特质对象
    println!("1. 创建特质对象:");
    let shapes: Vec<Box<dyn Drawable>> = vec![
        Box::new(Circle { radius: 5.0, center: (0.0, 0.0) }),
        Box::new(Rectangle { width: 10.0, height: 5.0, position: (1.0, 1.0) }),
        Box::new(Triangle { points: [(0.0, 0.0), (1.0, 0.0), (0.5, 1.0)] }),
    ];
    
    // 动态分发
    println!("\n2. 动态分发:");
    for (i, shape) in shapes.iter().enumerate() {
        println!("Shape {} ({}):", i, shape.type_name());
        shape.draw();
        println!("Info: {}", shape.get_info());
    }
    
    // 画布管理
    println!("\n3. 画布管理:");
    let mut canvas = DrawingCanvas::new();
    for shape in shapes {
        canvas.add_shape(shape);
    }
    canvas.draw_all();
    
    // 生命周期管理
    println!("\n4. 生命周期管理:");
    let objects: Vec<Box<dyn LifecycleManager>> = vec![
        Box::new(ManagedObject { name: "Object1".to_string(), alive: true }),
        Box::new(ManagedObject { name: "Object2".to_string(), alive: false }),
    ];
    
    for obj in &objects {
        println!("Object: {}, Alive: {}", obj.get_name(), obj.is_alive());
    }
    
    // 错误处理
    println!("\n5. 错误处理:");
    let handlers: Vec<Box<dyn ErrorHandler>> = vec![
        Box::new(ConsoleErrorHandler),
        Box::new(FileErrorHandler { file_path: "/tmp/errors.log".to_string() }),
    ];
    
    for handler in &handlers {
        let _ = handler.handle_error("Test error message");
    }
    
    // 序列化
    println!("\n6. 序列化:");
    let circle = Circle { radius: 3.0, center: (1.0, 2.0) };
    let serialized = circle.serialize();
    println!("Serialized: {}", serialized);
    
    let deserialized = Serializable::deserialize(&serialized);
    match deserialized {
        Ok(obj) => println!("Deserialized successfully"),
        Err(e) => println!("Deserialization error: {}", e),
    }
    
    // 性能测试
    println!("\n7. 性能测试:");
    let processors: Vec<Box<dyn Processor>> = vec![
        Box::new(FastProcessor),
        Box::new(SlowProcessor),
    ];
    
    for (i, processor) in processors.iter().enumerate() {
        let start = std::time::Instant::now();
        let result = processor.process();
        let duration = start.elapsed();
        println!("Processor {}: result={}, time={:?}", i, result, duration);
    }
} 