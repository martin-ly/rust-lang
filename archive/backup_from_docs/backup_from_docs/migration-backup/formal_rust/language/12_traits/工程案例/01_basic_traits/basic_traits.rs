//! 基础特质案例
//! 
//! 本模块演示特质系统的基础用法，包括特质定义、实现、约束和对象。
//! 
//! 理论映射：
//! - 特质声明: trait T { ... } → T = (N, M, A, C)
//! - 特质实现: impl T for Type → I = (T, τ, M')
//! - 特质约束: T: Display → B = (α, T)
//! - 特质对象: Box<dyn T> → O = (T, v, d)

/// 基础特质定义
/// 
/// 理论映射：T = (N, M, A, C)
/// - N: "Drawable" (特质名称)
/// - M: { draw(&self) } (方法签名集合)
/// - A: {} (关联类型集合)
/// - C: {} (约束条件集合)
pub trait Drawable {
    /// 绘制方法
    /// 
    /// 理论映射：方法签名 m ∈ M(T)
    fn draw(&self);
    
    /// 获取绘制信息
    /// 
    /// 理论映射：方法签名 m ∈ M(T)
    fn get_info(&self) -> String {
        "Drawable object".to_string()
    }
}

/// 圆形类型
/// 
/// 理论映射：τ = Circle
pub struct Circle {
    pub radius: f64,
    pub center: (f64, f64),
}

/// 特质实现
/// 
/// 理论映射：I = (T, τ, M')
/// - T: Drawable
/// - τ: Circle
/// - M': { draw(&self), get_info(&self) }
impl Drawable for Circle {
    fn draw(&self) {
        println!("Drawing circle with radius {} at ({}, {})", 
                 self.radius, self.center.0, self.center.1);
    }
    
    fn get_info(&self) -> String {
        format!("Circle: radius={}, center=({}, {})", 
                self.radius, self.center.0, self.center.1)
    }
}

/// 矩形类型
/// 
/// 理论映射：τ = Rectangle
pub struct Rectangle {
    pub width: f64,
    pub height: f64,
    pub position: (f64, f64),
}

/// 特质实现
/// 
/// 理论映射：I = (T, τ, M')
/// - T: Drawable
/// - τ: Rectangle
/// - M': { draw(&self), get_info(&self) }
impl Drawable for Rectangle {
    fn draw(&self) {
        println!("Drawing rectangle {}x{} at ({}, {})", 
                 self.width, self.height, self.position.0, self.position.1);
    }
    
    fn get_info(&self) -> String {
        format!("Rectangle: {}x{}, position=({}, {})", 
                self.width, self.height, self.position.0, self.position.1)
    }
}

/// 泛型函数与特质约束
/// 
/// 理论映射：B = (α, T)
/// - α: T (类型参数)
/// - T: Drawable (特质约束)
pub fn draw_object<T: Drawable>(obj: &T) {
    println!("Drawing object: {}", obj.get_info());
    obj.draw();
}

/// 特质对象使用
/// 
/// 理论映射：O = (T, v, d)
/// - T: Drawable
/// - v: 虚函数表
/// - d: 数据指针
pub fn draw_objects(objects: &[Box<dyn Drawable>]) {
    for (i, obj) in objects.iter().enumerate() {
        println!("Object {}: {}", i, obj.get_info());
        obj.draw();
    }
}

/// 特质约束组合
/// 
/// 理论映射：B = (α, T₁ + T₂)
/// - α: T (类型参数)
/// - T₁: Drawable
/// - T₂: std::fmt::Display
pub fn print_and_draw<T>(obj: &T) 
where 
    T: Drawable + std::fmt::Display,
{
    println!("Display: {}", obj);
    obj.draw();
}

/// 默认实现示例
/// 
/// 理论映射：默认实现提供通用行为
pub trait Animal {
    fn name(&self) -> &str;
    
    /// 默认实现
    /// 
    /// 理论映射：fn method(self) → R { default }
    fn make_sound(&self) {
        println!("{} makes a sound", self.name());
    }
    
    fn describe(&self) -> String {
        format!("Animal: {}", self.name())
    }
}

/// 狗类型
pub struct Dog {
    pub name: String,
}

impl Animal for Dog {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn make_sound(&self) {
        println!("{} says: Woof!", self.name);
    }
}

/// 猫类型
pub struct Cat {
    pub name: String,
}

impl Animal for Cat {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn make_sound(&self) {
        println!("{} says: Meow!", self.name);
    }
}

/// 特质作为参数
/// 
/// 理论映射：特质作为函数参数类型
pub fn animal_sounds(animals: &[Box<dyn Animal>]) {
    for animal in animals {
        animal.make_sound();
        println!("Description: {}", animal.describe());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 测试基础特质实现
    #[test]
    fn test_basic_trait_implementation() {
        let circle = Circle { radius: 5.0, center: (0.0, 0.0) };
        let rectangle = Rectangle { width: 10.0, height: 5.0, position: (1.0, 1.0) };
        
        // 测试特质方法调用
        circle.draw();
        rectangle.draw();
        
        // 测试信息获取
        assert!(circle.get_info().contains("Circle"));
        assert!(rectangle.get_info().contains("Rectangle"));
    }

    /// 测试泛型函数
    #[test]
    fn test_generic_function() {
        let circle = Circle { radius: 3.0, center: (0.0, 0.0) };
        let rectangle = Rectangle { width: 4.0, height: 6.0, position: (0.0, 0.0) };
        
        // 测试特质约束
        draw_object(&circle);
        draw_object(&rectangle);
    }

    /// 测试特质对象
    #[test]
    fn test_trait_objects() {
        let objects: Vec<Box<dyn Drawable>> = vec![
            Box::new(Circle { radius: 2.0, center: (0.0, 0.0) }),
            Box::new(Rectangle { width: 3.0, height: 4.0, position: (1.0, 1.0) }),
        ];
        
        draw_objects(&objects);
    }

    /// 测试动物特质
    #[test]
    fn test_animal_trait() {
        let dog = Dog { name: "Buddy".to_string() };
        let cat = Cat { name: "Whiskers".to_string() };
        
        // 测试默认实现
        dog.make_sound();
        cat.make_sound();
        
        // 测试描述方法
        assert!(dog.describe().contains("Buddy"));
        assert!(cat.describe().contains("Whiskers"));
    }

    /// 测试特质对象集合
    #[test]
    fn test_trait_object_collection() {
        let animals: Vec<Box<dyn Animal>> = vec![
            Box::new(Dog { name: "Rex".to_string() }),
            Box::new(Cat { name: "Fluffy".to_string() }),
        ];
        
        animal_sounds(&animals);
    }
}

/// 示例用法
pub fn run_examples() {
    println!("=== 基础特质案例 ===");
    
    // 创建对象
    let circle = Circle { radius: 5.0, center: (0.0, 0.0) };
    let rectangle = Rectangle { width: 10.0, height: 5.0, position: (1.0, 1.0) };
    
    // 直接调用特质方法
    println!("直接调用:");
    circle.draw();
    rectangle.draw();
    
    // 使用泛型函数
    println!("\n泛型函数:");
    draw_object(&circle);
    draw_object(&rectangle);
    
    // 使用特质对象
    println!("\n特质对象:");
    let objects: Vec<Box<dyn Drawable>> = vec![
        Box::new(circle),
        Box::new(rectangle),
    ];
    draw_objects(&objects);
    
    // 动物示例
    println!("\n动物特质:");
    let dog = Dog { name: "Buddy".to_string() };
    let cat = Cat { name: "Whiskers".to_string() };
    
    dog.make_sound();
    cat.make_sound();
    
    let animals: Vec<Box<dyn Animal>> = vec![
        Box::new(dog),
        Box::new(cat),
    ];
    animal_sounds(&animals);
} 