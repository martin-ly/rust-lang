//! 泛型模块集成测试套件 / Generics Module Integration Test Suite

/// 测试泛型函数集成
#[test]
fn test_generic_function_integration() {
    fn identity<T>(x: T) -> T {
        x
    }

    assert_eq!(identity(5), 5);
    assert_eq!(identity("hello"), "hello");
}

/// 测试泛型结构体集成
#[test]
fn test_generic_struct_integration() {
    struct Container<T> {
        value: T,
    }

    let int_container = Container { value: 42 };
    let str_container = Container { value: "hello" };

    assert_eq!(int_container.value, 42);
    assert_eq!(str_container.value, "hello");
}

/// 测试Trait约束集成
#[test]
fn test_trait_bound_integration() {
    trait Display {
        fn display(&self) -> String;
    }

    impl Display for i32 {
        fn display(&self) -> String {
            format!("{}", self)
        }
    }

    fn show<T: Display>(item: T) -> String {
        item.display()
    }

    assert_eq!(show(42), "42");
}

/// 测试泛型枚举集成
#[test]
fn test_generic_enum_integration() {
    enum Option<T> {
        Some(T),
        None,
    }

    let some_value: Option<i32> = Option::Some(42);
    let none_value: Option<i32> = Option::None;

    match some_value {
        Option::Some(x) => assert_eq!(x, 42),
        Option::None => panic!("Expected Some"),
    }

    match none_value {
        Option::Some(_) => panic!("Expected None"),
        Option::None => assert!(true),
    }
}

/// 测试关联类型集成
#[test]
fn test_associated_type_integration() {
    trait Iterator {
        type Item;

        fn next(&mut self) -> Option<Self::Item>;
    }

    struct Counter {
        count: u32,
    }

    impl Iterator for Counter {
        type Item = u32;

        fn next(&mut self) -> Option<Self::Item> {
            self.count += 1;
            Some(self.count)
        }
    }

    let mut counter = Counter { count: 0 };
    assert_eq!(counter.next(), Some(1));
}

/// 测试泛型方法集成
#[test]
fn test_generic_method_integration() {
    struct Point<T> {
        x: T,
        y: T,
    }

    impl<T> Point<T> {
        fn new(x: T, y: T) -> Self {
            Point { x, y }
        }

        fn get_x(&self) -> &T {
            &self.x
        }
    }

    let point = Point::new(1.0, 2.0);
    assert_eq!(*point.get_x(), 1.0);
}
