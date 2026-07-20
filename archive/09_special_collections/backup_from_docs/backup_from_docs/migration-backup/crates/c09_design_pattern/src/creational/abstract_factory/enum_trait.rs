#[allow(unused)]
trait Shape {
    fn draw(&self);
}

#[allow(unused)]
struct Circle {
    radius: f64,
}

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

impl Shape for Rectangle {
    fn draw(&self) {
        println!(
            "Drawing a Rectangle with width: {} and height: {}",
            self.width, self.height
        );
    }
}

#[allow(unused)]
trait ShapeFactory {
    fn create_shape(&self) -> Box<dyn Shape>;
}

#[allow(unused)]
struct CircleFactory;

impl ShapeFactory for CircleFactory {
    fn create_shape(&self) -> Box<dyn Shape> {
        Box::new(Circle { radius: 5.0 })
    }
}

#[allow(unused)]
struct RectangleFactory;

impl ShapeFactory for RectangleFactory {
    fn create_shape(&self) -> Box<dyn Shape> {
        Box::new(Rectangle {
            width: 4.0,
            height: 3.0,
        })
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
