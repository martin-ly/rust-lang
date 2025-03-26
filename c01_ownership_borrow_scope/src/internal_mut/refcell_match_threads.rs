use std::cell::RefCell;
use std::sync::{Arc, Mutex};

/*
match表达式在Rust中不仅可以用于匹配外部可变性，也可以用于匹配内部可变性。
RefCell是实现内部可变性的一种方式，但并不是唯一的解决方案。
你可以使用其他类型（如Mutex、RwLock等）来实现内部可变性，并在match表达式中进行匹配。

内部可变性与match表达式
    match表达式可以用于匹配包含内部可变性类型的结构体或枚举。
    无论是使用RefCell、Mutex还是RwLock，你都可以在match中处理这些类型的值。
*/


struct Point {
    x: RefCell<i32>,
    y: RefCell<i32>,
}

impl Point {
    fn new(x: i32, y: i32) -> Self {
        Point {
            x: RefCell::new(x),
            y: RefCell::new(y),
        }
    }

    fn move_by(&self, dx: i32, dy: i32) {
        *self.x.borrow_mut() += dx;
        *self.y.borrow_mut() += dy;
    }

    fn get_position(&self) -> (i32, i32) {
        (*self.x.borrow(), *self.y.borrow())
    }
}

enum Shape {
    Circle(Point),
    Rectangle(Point, Point),
    ThreadSafeCircle(Arc<Mutex<Point>>),
}

impl Shape {
    fn move_shape(&self, dx: i32, dy: i32) {
        match self {
            Shape::Circle(point) => point.move_by(dx, dy),
            Shape::Rectangle(top_left, bottom_right) => {
                top_left.move_by(dx, dy);
                bottom_right.move_by(dx, dy);
            }
            Shape::ThreadSafeCircle(point) => {
                let p = point.lock().unwrap();
                p.move_by(dx, dy);
            }
        }
    }

    fn get_shape_position(&self) -> Vec<(i32, i32)> {
        match self {
            Shape::Circle(point) => vec![point.get_position()],
            Shape::Rectangle(top_left, bottom_right) => {
                vec![top_left.get_position(), bottom_right.get_position()]
            }
            Shape::ThreadSafeCircle(point) => {
                let p = point.lock().unwrap();
                vec![p.get_position()]
            }
        }
    }
}

/*
解释
    Point结构体：
        使用RefCell<i32>来存储x和y坐标，允许在不可变上下文中修改它们。
    Shape枚举：
        定义了三种形状：Circle、Rectangle和ThreadSafeCircle，
        后者使用Arc<Mutex<Point>>来实现线程安全的内部可变性。
    move_shape方法：
        使用match表达式，根据形状的类型调用相应的移动方法，支持内部可变性。
    get_shape_position方法：
        返回形状的当前坐标，使用match表达式处理不同的形状类型。
    主函数：创建不同类型的形状，移动它们并打印最终位置。
*/

#[allow(unused)]
fn refcell_match_threads() {
    let circle = Shape::Circle(Point::new(0, 0));
    let rectangle = Shape::Rectangle(Point::new(1, 1), Point::new(3, 3));
    let thread_safe_circle = Shape::ThreadSafeCircle(Arc::new(Mutex::new(Point::new(2, 2))));

    circle.move_shape(5, 5);
    rectangle.move_shape(2, 2);
    thread_safe_circle.move_shape(1, 1);

    let circle_positions = circle.get_shape_position();
    let rectangle_positions = rectangle.get_shape_position();
    let thread_safe_circle_positions = thread_safe_circle.get_shape_position();

    println!("Circle Position: {:?}", circle_positions); // 输出: Circle Position: [(5, 5)]
    println!("Rectangle Positions: {:?}", rectangle_positions); // 输出: Rectangle Positions: [(3, 3), (5, 5)]
    println!("Thread Safe Circle Position: {:?}", thread_safe_circle_positions); // 输出: Thread Safe Circle Position: [(3, 3)]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_refcell_match_threads01() {
        refcell_match_threads();
    }
}
