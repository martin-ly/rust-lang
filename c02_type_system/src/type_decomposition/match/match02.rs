
// 定义一个 Trait，表示图形
trait Shape {
    fn area(&self) -> f64; // 计算面积
    fn draw(&self); // 绘制图形
}

// 定义一个圆形结构体
#[allow(unused)]
pub struct Circle {
    pub radius: f64,
}

impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }

    fn draw(&self) {
        println!("Drawing a Circle with radius: {}", self.radius);
    }
}

// 定义一个矩形结构体
#[allow(unused)]
pub struct Rectangle {
    pub width: f64,
    pub height: f64,
}

impl Shape for Rectangle {
    fn area(&self) -> f64 {
        self.width * self.height
    }

    fn draw(&self) {
        println!("Drawing a Rectangle with width: {} and height: {}", self.width, self.height);
    }
}

// 定义一个枚举，用于存储不同类型的图形
#[allow(unused)]
pub enum ShapeEnum {
    Circle(Circle),
    Rectangle(Rectangle),
}

impl ShapeEnum {
    pub fn area(&self) -> f64 {
        match self {
            ShapeEnum::Circle(circle) => circle.area(),
            ShapeEnum::Rectangle(rectangle) => rectangle.area(),
        }
    }

   pub  fn draw(&self) {
        match self {
            ShapeEnum::Circle(circle) => circle.draw(),
            ShapeEnum::Rectangle(rectangle) => rectangle.draw(),
        }
    }
}

