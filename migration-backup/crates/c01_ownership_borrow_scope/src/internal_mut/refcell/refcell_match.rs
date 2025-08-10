use std::cell::RefCell;

/*
在Rust中，结合使用RefCell、struct、enum、tuple以及impl和match表达式，可以创建灵活且强大的数据结构。
这种组合允许在不可变上下文中实现内部可变性，并根据不同的类型或状态进行处理。以下是一些可能的组合和示例。

可能的组合
    使用RefCell的struct：
        在结构体中使用RefCell来实现内部可变性。
    使用enum来表示不同的状态：
        可以定义一个enum，其中的每个变体都可以包含一个或多个struct或tuple。
    在impl中定义方法：
        为struct或enum实现方法，使用match表达式根据不同的变体或状态进行处理。
    结合tuple：
        可以在struct或enum中使用元组来存储多个值。
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
}

impl Shape {
    fn move_shape(&self, dx: i32, dy: i32) {
        match self {
            Shape::Circle(point) => point.move_by(dx, dy),
            Shape::Rectangle(top_left, bottom_right) => {
                top_left.move_by(dx, dy);
                bottom_right.move_by(dx, dy);
            }
        }
    }

    fn get_shape_position(&self) -> Vec<(i32, i32)> {
        match self {
            Shape::Circle(point) => vec![point.get_position()],
            Shape::Rectangle(top_left, bottom_right) => {
                vec![top_left.get_position(), bottom_right.get_position()]
            }
        }
    }
}

/*
解释
    Point结构体：
        使用RefCell<i32>来存储x和y坐标，允许在不可变上下文中修改它们。
    Shape枚举：
        定义了两种形状：Circle和Rectangle，每种形状都可以包含一个或多个Point。
    move_shape方法：
        使用match表达式，根据形状的类型调用相应的move_by方法，修改内部状态。
    get_shape_position方法：
        返回形状的当前坐标，使用match表达式处理不同的形状类型。
    主函数：
        创建一个圆和一个矩形，移动它们并打印最终位置。
*/
#[allow(unused)]
fn refcell_match() {
    let circle = Shape::Circle(Point::new(0, 0));
    let rectangle = Shape::Rectangle(Point::new(1, 1), Point::new(3, 3));

    circle.move_shape(5, 5);
    rectangle.move_shape(2, 2);

    let circle_positions = circle.get_shape_position();
    let rectangle_positions = rectangle.get_shape_position();

    // 输出: Circle Position: [(5, 5)]
    println!("Circle Position: {:?}", circle_positions);
    // 输出: Rectangle Positions: [(3, 3), (5, 5)]
    println!("Rectangle Positions: {:?}", rectangle_positions);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_refcell_match01() {
        refcell_match();
    }
}
