#[allow(unused)]
trait Shape {
    fn draw(&self);
}

#[allow(unused)]
struct Circle {
    radius: f64,
}

#[allow(unused)]
impl Shape for Circle {
    fn draw(&self) {
        println!("Drawing a Circle with radius: {}", self.radius);
    }
}

#[allow(unused)]
struct Rectangle {
    width: f64,
    height: f64,
}

#[allow(unused)]
impl Shape for Rectangle {
    fn draw(&self) {
        println!(
            "Drawing a Rectangle with width: {} and height: {}",
            self.width, self.height
        );
    }
}

#[allow(unused)]
trait ShapeFactory<T: Shape> {
    fn create_shape(&self) -> T;
}

#[allow(unused)]
struct CircleFactory;

#[allow(unused)]
impl ShapeFactory<Circle> for CircleFactory {
    fn create_shape(&self) -> Circle {
        Circle { radius: 5.0 }
    }
}

#[allow(unused)]
struct RectangleFactory;

#[allow(unused)]
impl ShapeFactory<Rectangle> for RectangleFactory {
    fn create_shape(&self) -> Rectangle {
        Rectangle {
            width: 4.0,
            height: 3.0,
        }
    }
}

#[allow(unused)]
pub fn test_abstract_factory() {
    let circle_factory = CircleFactory;
    let rectangle_factory = RectangleFactory;

    let circle = circle_factory.create_shape();
    let rectangle = rectangle_factory.create_shape();

    circle.draw(); // 输出: Drawing a Circle with radius: 5
    rectangle.draw(); // 输出: Drawing a Rectangle with width: 4 and height: 3
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abstract_factory01() {
        test_abstract_factory();
    }
    
    #[test]
    fn test_circle_factory() {
        let factory = CircleFactory;
        let circle = factory.create_shape();
        assert_eq!(circle.radius, 5.0);
    }
    
    #[test]
    fn test_rectangle_factory() {
        let factory = RectangleFactory;
        let rectangle = factory.create_shape();
        assert_eq!(rectangle.width, 4.0);
        assert_eq!(rectangle.height, 3.0);
    }
}