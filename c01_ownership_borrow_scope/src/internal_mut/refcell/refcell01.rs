use std::cell::RefCell;

/*
设计思路
    使用RefCell：
        对于需要在不可变上下文中修改的字段，可以使用RefCell来实现内部可变性。
    实现impl方法：
        在impl块中定义方法时，可以使用&self或&mut self来控制对结构体的访问。
    结合enum和struct：
        可以在enum中使用不同的struct，并在实现方法时根据不同的变体进行处理。
    使用元组：
        元组可以作为简单的数据结构，结合内部可变性来实现更复杂的逻辑。
*/

#[allow(unused)]
struct Point {
    x: RefCell<i32>,
    y: RefCell<i32>,
}

#[allow(unused)]
impl Point {
    fn new(x: i32, y: i32) -> Self {
        Point {
            x: RefCell::new(x),
            y: RefCell::new(y),
        }
    }

    fn move_by(&self, dx: i32, dy: i32) {
        // 使用ref mut self来修改内部状态
        *self.x.borrow_mut() += dx;
        *self.y.borrow_mut() += dy;
    }

    fn get_position(&self) -> (i32, i32) {
        (*self.x.borrow(), *self.y.borrow())
    }
}

#[allow(unused)]
enum Shape {
    Circle(Point),
    Rectangle(Point, Point),
}

#[allow(unused)]
impl Shape {
    fn move_shape(&mut self, dx: i32, dy: i32) {
        match self {
            Shape::Circle(point) => point.move_by(dx, dy),
            Shape::Rectangle(top_left, bottom_right) => {
                top_left.move_by(dx, dy);
                bottom_right.move_by(dx, dy);
            }
        }
    }
}

#[allow(unused)]
fn refcell_test() {
    let mut circle = Shape::Circle(Point::new(0, 0));
    circle.move_shape(5, 5);
    
    if let Shape::Circle(point) = circle {
        let (x, y) = point.get_position();
        // 输出: Circle Position: (5, 5)
        println!("Circle Position: ({}, {})", x, y); 
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_refcell01() {
        refcell_test();
    }
}

