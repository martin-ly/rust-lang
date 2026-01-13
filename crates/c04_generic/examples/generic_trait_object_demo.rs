//! Trait对象与泛型对比示例
//!
//! 本示例展示Trait对象（动态分派）与泛型（静态分派）的对比：
//! - 静态分派 vs 动态分派
//! - 性能对比
//! - 使用场景选择
//!
//! 运行方式:
//! ```bash
//! cargo run --example generic_trait_object_demo
//! ```

use std::time::Instant;

/// 形状trait
trait Shape {
    fn area(&self) -> f64;
    fn describe(&self) -> String;
}

/// 圆形
struct Circle {
    radius: f64,
}

impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }

    fn describe(&self) -> String {
        format!("圆形 (半径: {})", self.radius)
    }
}

/// 矩形
struct Rectangle {
    width: f64,
    height: f64,
}

impl Shape for Rectangle {
    fn area(&self) -> f64 {
        self.width * self.height
    }

    fn describe(&self) -> String {
        format!("矩形 (宽: {}, 高: {})", self.width, self.height)
    }
}

/// 使用泛型（静态分派）
fn calculate_area_generic<T: Shape>(shape: &T) -> f64 {
    shape.area()
}

/// 使用Trait对象（动态分派）
fn calculate_area_dynamic(shape: &dyn Shape) -> f64 {
    shape.area()
}

fn main() {
    println!("🚀 Trait对象与泛型对比示例\n");
    println!("{}", "=".repeat(60));

    // 创建形状
    let circle = Circle { radius: 5.0 };
    let rectangle = Rectangle {
        width: 10.0,
        height: 8.0,
    };

    // 1. 静态分派（泛型）
    println!("\n📊 静态分派（泛型）:");
    println!("{}", "-".repeat(60));
    let area1 = calculate_area_generic(&circle);
    let area2 = calculate_area_generic(&rectangle);
    println!("圆形面积: {:.2}", area1);
    println!("矩形面积: {:.2}", area2);

    // 2. 动态分派（Trait对象）
    println!("\n📊 动态分派（Trait对象）:");
    println!("{}", "-".repeat(60));
    let area3 = calculate_area_dynamic(&circle as &dyn Shape);
    let area4 = calculate_area_dynamic(&rectangle as &dyn Shape);
    println!("圆形面积: {:.2}", area3);
    println!("矩形面积: {:.2}", area4);

    // 3. 异构集合（只能用Trait对象）
    println!("\n📊 异构集合（Trait对象）:");
    println!("{}", "-".repeat(60));
    let shapes: Vec<Box<dyn Shape>> = vec![
        Box::new(Circle { radius: 3.0 }),
        Box::new(Rectangle {
            width: 4.0,
            height: 5.0,
        }),
        Box::new(Circle { radius: 2.0 }),
        Box::new(Rectangle {
            width: 6.0,
            height: 7.0,
        }),
    ];

    for (i, shape) in shapes.iter().enumerate() {
        println!(
            "形状 {}: {}，面积: {:.2}",
            i + 1,
            shape.describe(),
            shape.area()
        );
    }

    // 4. 性能对比
    println!("\n⚡ 性能对比:");
    println!("{}", "-".repeat(60));

    let iterations = 1_000_000;

    // 静态分派
    let start = Instant::now();
    for _ in 0..iterations {
        calculate_area_generic(&circle);
    }
    let static_time = start.elapsed();

    // 动态分派
    let start = Instant::now();
    for _ in 0..iterations {
        calculate_area_dynamic(&circle as &dyn Shape);
    }
    let dynamic_time = start.elapsed();

    println!("静态分派耗时: {:?}", static_time);
    println!("动态分派耗时: {:?}", dynamic_time);
    println!(
        "性能差异: {:.2}x",
        dynamic_time.as_nanos() as f64 / static_time.as_nanos() as f64
    );

    // 5. 使用场景总结
    println!("\n📝 使用场景总结:");
    println!("{}", "-".repeat(60));
    println!("静态分派（泛型）适用于:");
    println!("  ✅ 编译时类型已知");
    println!("  ✅ 性能敏感的代码");
    println!("  ✅ 需要零成本抽象");
    println!("\n动态分派（Trait对象）适用于:");
    println!("  ✅ 需要在集合中存储不同类型");
    println!("  ✅ 运行时多态（插件系统）");
    println!("  ✅ 类型数量很多（减少二进制大小）");

    println!("\n✅ 演示完成！");
}
