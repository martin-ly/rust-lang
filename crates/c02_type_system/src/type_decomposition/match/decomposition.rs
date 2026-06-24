//! `match` 与模式解构：把组合类型拆回组成部分。

/// 消息枚举。
pub enum Message {
    /// 问候消息。
    Hello { id: i32 },
    /// 告别消息。
    Goodbye { id: i32 },
}

/// 处理消息，展示绑定守卫（binding guard）。
pub fn process_message(msg: Message) -> &'static str {
    match msg {
        Message::Hello { id: _id @ 1..=10 } => "hello-small",
        Message::Hello { .. } => "hello-other",
        Message::Goodbye { .. } => "goodbye",
    }
}

/// FizzBuzz：用元组模式匹配同时判断多个条件。
pub fn fizz_buzz(n: u32) -> String {
    match (n % 3, n % 5) {
        (0, 0) => "FizzBuzz".to_string(),
        (0, _) => "Fizz".to_string(),
        (_, 0) => "Buzz".to_string(),
        (_, _) => n.to_string(),
    }
}

/// 形状接口。
pub trait Shape {
    /// 计算面积。
    fn area(&self) -> f64;
}

/// 圆。
pub struct Circle {
    /// 半径。
    pub radius: f64,
}

impl Circle {
    /// 绘制圆。
    pub fn draw(&self) {
        println!("Drawing circle with radius {}", self.radius);
    }
}

impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }
}

/// 矩形。
pub struct Rectangle {
    /// 宽度。
    pub width: f64,
    /// 高度。
    pub height: f64,
}

impl Rectangle {
    /// 绘制矩形。
    pub fn draw(&self) {
        println!("Drawing rectangle {}x{}", self.width, self.height);
    }
}

impl Shape for Rectangle {
    fn area(&self) -> f64 {
        self.width * self.height
    }
}

/// 形状和类型。
pub enum ShapeEnum {
    /// 圆。
    Circle(Circle),
    /// 矩形。
    Rectangle(Rectangle),
}

impl ShapeEnum {
    /// 绘制图形。
    pub fn draw(&self) {
        match self {
            ShapeEnum::Circle(c) => c.draw(),
            ShapeEnum::Rectangle(r) => r.draw(),
        }
    }

    /// 计算面积。
    pub fn area(&self) -> f64 {
        match self {
            ShapeEnum::Circle(c) => c.area(),
            ShapeEnum::Rectangle(r) => r.area(),
        }
    }
}

/// 带守卫的 `match`：判断奇偶。
pub fn match_guard(x: u32) {
    match x {
        x if x % 2 == 0 => println!("Even"),
        _ => println!("Odd"),
    }
}

/// 穷尽性检查示例：如果遗漏 `None` 分支，编译器会报错。
///
/// ```compile_fail
/// pub fn non_exhaustive(o: Option<i32>) -> i32 {
///     match o {
///         Some(v) => v,
///     }
/// }
/// ```
pub fn exhaustive_match(o: Option<i32>) -> i32 {
    o.unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_process_message() {
        assert_eq!(process_message(Message::Hello { id: 5 }), "hello-small");
        assert_eq!(process_message(Message::Hello { id: 100 }), "hello-other");
        assert_eq!(process_message(Message::Goodbye { id: 1 }), "goodbye");
    }

    #[test]
    fn test_fizz_buzz() {
        assert_eq!(fizz_buzz(15), "FizzBuzz");
        assert_eq!(fizz_buzz(3), "Fizz");
        assert_eq!(fizz_buzz(5), "Buzz");
        assert_eq!(fizz_buzz(7), "7");
    }

    #[test]
    fn test_shape_enum_area() {
        let circle = ShapeEnum::Circle(Circle { radius: 1.0 });
        let rect = ShapeEnum::Rectangle(Rectangle {
            width: 2.0,
            height: 3.0,
        });
        assert!((circle.area() - std::f64::consts::PI).abs() < 1e-10);
        assert!((rect.area() - 6.0).abs() < 1e-10);
    }

    #[test]
    fn test_exhaustive_match() {
        assert_eq!(exhaustive_match(Some(7)), 7);
        assert_eq!(exhaustive_match(None), 0);
    }
}
