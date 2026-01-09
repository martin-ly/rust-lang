//! 泛型模块测试套件

#[test]
fn test_generic_stack() {
    use std::collections::VecDeque;

    // 测试泛型栈的基本操作
    let mut stack: VecDeque<i32> = VecDeque::new();
    stack.push_back(1);
    stack.push_back(2);
    stack.push_back(3);

    assert_eq!(stack.len(), 3);
    assert_eq!(stack.pop_back(), Some(3));
    assert_eq!(stack.pop_back(), Some(2));
    assert_eq!(stack.pop_back(), Some(1));
    assert_eq!(stack.pop_back(), None);
}

#[test]
fn test_generic_queue() {
    use std::collections::VecDeque;

    // 测试泛型队列的基本操作
    let mut queue: VecDeque<&str> = VecDeque::new();
    queue.push_back("first");
    queue.push_back("second");
    queue.push_back("third");

    assert_eq!(queue.len(), 3);
    assert_eq!(queue.pop_front(), Some("first"));
    assert_eq!(queue.pop_front(), Some("second"));
    assert_eq!(queue.pop_front(), Some("third"));
    assert_eq!(queue.pop_front(), None);
}

#[test]
fn test_type_parameter() {
    // 测试泛型类型参数
    fn identity<T>(value: T) -> T {
        value
    }

    assert_eq!(identity(42), 42);
    assert_eq!(identity("hello"), "hello");
    assert_eq!(identity(true), true);
}

#[test]
fn test_trait_bound() {
    // 测试 trait 边界
    fn print_debug<T: std::fmt::Debug>(value: T) -> String {
        format!("{:?}", value)
    }

    assert_eq!(print_debug(42), "42");
    assert_eq!(print_debug("test"), "\"test\"");
    assert_eq!(print_debug(vec![1, 2, 3]), "[1, 2, 3]");
}

#[test]
fn test_associated_type() {
    // 测试关联类型
    trait Container {
        type Item;
        fn get(&self) -> Option<&Self::Item>;
    }

    struct MyContainer<T> {
        value: Option<T>,
    }

    impl<T> Container for MyContainer<T> {
        type Item = T;
        fn get(&self) -> Option<&Self::Item> {
            self.value.as_ref()
        }
    }

    let container = MyContainer { value: Some(42) };
    assert_eq!(container.get(), Some(&42));
}

#[test]
fn test_generic_function() {
    // 测试泛型函数
    fn find_max<T: PartialOrd>(items: &[T]) -> Option<&T> {
        items.iter().max_by(|a, b| a.partial_cmp(b).unwrap())
    }

    let numbers = vec![1, 5, 3, 9, 2];
    assert_eq!(find_max(&numbers), Some(&9));

    let strings = vec!["apple", "banana", "cherry"];
    assert_eq!(find_max(&strings), Some(&"cherry"));
}

#[test]
fn test_generic_struct() {
    // 测试泛型结构体
    struct Pair<T, U> {
        first: T,
        second: U,
    }

    let pair = Pair {
        first: 42,
        second: "hello",
    };

    assert_eq!(pair.first, 42);
    assert_eq!(pair.second, "hello");
}

#[test]
fn test_generic_enum() {
    // 测试泛型枚举
    enum Result<T, E> {
        Ok(T),
        Err(E),
    }

    let ok: Result<i32, &str> = Result::Ok(42);
    let err: Result<i32, &str> = Result::Err("error");

    match ok {
        Result::Ok(value) => assert_eq!(value, 42),
        Result::Err(_) => panic!("Should be Ok"),
    }

    match err {
        Result::Ok(_) => panic!("Should be Err"),
        Result::Err(msg) => assert_eq!(msg, "error"),
    }
}

#[test]
fn test_const_generics() {
    // 测试常量泛型（Rust 1.51+）
    struct Array<T, const N: usize> {
        data: [T; N],
    }

    let arr = Array {
        data: [1, 2, 3, 4, 5],
    };

    assert_eq!(arr.data.len(), 5);
    assert_eq!(arr.data[0], 1);
    assert_eq!(arr.data[4], 5);
}
