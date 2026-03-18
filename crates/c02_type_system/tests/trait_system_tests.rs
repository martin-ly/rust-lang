//! Trait系统测试
//!
//! 测试Rust的trait系统：
//! - 基本trait定义和实现
//! - trait边界
//! - 关联类型
//! - trait对象

/// 测试基本trait定义和实现
#[test]
fn test_basic_trait() {
    trait Drawable {
        fn draw(&self) -> String;
    }
    
    struct Circle {
        radius: f64,
    }
    
    impl Drawable for Circle {
        fn draw(&self) -> String {
            format!("Circle with radius {}", self.radius)
        }
    }
    
    let circle = Circle { radius: 5.0 };
    assert_eq!(circle.draw(), "Circle with radius 5");
}

/// 测试默认trait方法
#[test]
fn test_default_trait_methods() {
    trait Greet {
        fn greet(&self) -> String {
            String::from("Hello!")
        }
        
        fn greet_with_name(&self, name: &str) -> String {
            format!("Hello, {}!", name)
        }
    }
    
    struct Person;
    impl Greet for Person {}
    
    let person = Person;
    assert_eq!(person.greet(), "Hello!");
    assert_eq!(person.greet_with_name("Alice"), "Hello, Alice!");
}

/// 测试trait继承
#[test]
fn test_trait_inheritance() {
    trait Animal {
        fn name(&self) -> &str;
    }
    
    trait Dog: Animal {
        fn bark(&self) -> String {
            format!("{} says: Woof!", self.name())
        }
    }
    
    struct Labrador;
    impl Animal for Labrador {
        fn name(&self) -> &str {
            "Labrador"
        }
    }
    impl Dog for Labrador {}
    
    let dog = Labrador;
    assert_eq!(dog.bark(), "Labrador says: Woof!");
}

/// 测试trait边界
#[test]
fn test_trait_bounds() {
    fn print_debug<T: std::fmt::Debug>(item: T) {
        println!("{:?}", item);
    }
    
    print_debug(42);
    print_debug("hello");
    print_debug(vec![1, 2, 3]);
}

/// 测试多重trait边界
#[test]
fn test_multiple_trait_bounds() {
    fn process<T>(item: T) 
    where
        T: std::fmt::Debug + Clone + PartialEq,
    {
        let cloned = item.clone();
        assert_eq!(item, cloned);
        println!("{:?}", item);
    }
    
    process(42);
    process(String::from("test"));
}

/// 测试关联类型
#[test]
fn test_associated_types() {
    trait Container {
        type Item;
        
        fn get(&self) -> Option<&Self::Item>;
        fn put(&mut self, item: Self::Item);
    }
    
    struct Box<T> {
        item: Option<T>,
    }
    
    impl<T> Container for Box<T> {
        type Item = T;
        
        fn get(&self) -> Option<&Self::Item> {
            self.item.as_ref()
        }
        
        fn put(&mut self, item: Self::Item) {
            self.item = Some(item);
        }
    }
    
    let mut box_item = Box { item: None };
    box_item.put(42);
    assert_eq!(box_item.get(), Some(&42));
}

/// 测试trait对象动态分发
#[test]
fn test_trait_objects() {
    trait Shape {
        fn area(&self) -> f64;
    }
    
    struct Rectangle {
        width: f64,
        height: f64,
    }
    
    struct Circle {
        radius: f64,
    }
    
    impl Shape for Rectangle {
        fn area(&self) -> f64 {
            self.width * self.height
        }
    }
    
    impl Shape for Circle {
        fn area(&self) -> f64 {
            std::f64::consts::PI * self.radius * self.radius
        }
    }
    
    let shapes: Vec<Box<dyn Shape>> = vec![
        Box::new(Rectangle { width: 3.0, height: 4.0 }),
        Box::new(Circle { radius: 2.0 }),
    ];
    
    assert_eq!(shapes[0].area(), 12.0);
    assert!((shapes[1].area() - 12.566).abs() < 0.01);
}

/// 测试泛型trait实现
#[test]
fn test_generic_trait_impl() {
    trait Wrapper<T> {
        fn get(&self) -> &T;
    }
    
    struct Container<T> {
        value: T,
    }
    
    impl<T> Wrapper<T> for Container<T> {
        fn get(&self) -> &T {
            &self.value
        }
    }
    
    let container = Container { value: 42 };
    assert_eq!(*container.get(), 42);
}

/// 测试trait的impl Trait返回类型
#[test]
fn test_impl_trait_return() {
    fn make_iter() -> impl Iterator<Item = i32> {
        vec![1, 2, 3].into_iter()
    }
    
    let sum: i32 = make_iter().sum();
    assert_eq!(sum, 6);
}
