use c02_type_system::type_decomposition::r#match::match02::*;

fn main() {
    // 创建不同类型的图形
    let shapes: Vec<ShapeEnum> = vec![
        ShapeEnum::Circle(Circle { radius: 5.0 }),
        ShapeEnum::Rectangle(Rectangle { width: 4.0, height: 3.0 }),
    ];

    // 遍历图形并调用方法
    for shape in shapes {
        shape.draw();
        println!("Area: {}", shape.area());
    }
}