//! 类型推断测试
//!
//! 测试Rust类型系统的核心特性：
//! - 类型推断
//! - 类型注解
//! - 泛型推断

/// 测试基本类型推断
#[test]
fn test_basic_type_inference() {
    // 整数类型推断
    let x = 42;
    assert_eq!(std::mem::size_of_val(&x), 4); // i32

    // 浮点数类型推断
    let y = 2.71;
    assert_eq!(std::mem::size_of_val(&y), 8); // f64

    // 字符串类型推断
    let s = "hello";
    assert_eq!(s.len(), 5);
}

/// 测试泛型类型推断
#[test]
fn test_generic_type_inference() {
    fn identity<T>(x: T) -> T {
        x
    }

    // 编译器自动推断T为i32
    let x = identity(42);
    assert_eq!(x, 42);

    // 编译器自动推断T为String
    let s = identity(String::from("test"));
    assert_eq!(s, "test");
}

/// 测试类型注解
#[test]
fn test_type_annotations() {
    // 显式类型注解
    let x: u32 = 42;
    assert_eq!(x, 42);

    // 复杂类型注解
    let v: Vec<i32> = vec![1, 2, 3];
    assert_eq!(v.len(), 3);

    // 泛型结构体类型注解
    let pair: (i32, String) = (1, String::from("one"));
    assert_eq!(pair.0, 1);
}

/// 测试类型转换
#[test]
fn test_type_coercion() {
    // 整数提升
    let x: i32 = 42;
    let y: i64 = x as i64;
    assert_eq!(y, 42);

    // 浮点数转换
    let f: f64 = 2.71;
    let i: i32 = f as i32;
    assert_eq!(i, 2);
}

/// 测试Option<T>类型操作
#[test]
fn test_option_type_operations() {
    let some_value: Option<i32> = Some(42);
    let none_value: Option<i32> = None;

    assert!(some_value.is_some());
    assert!(none_value.is_none());
    assert_eq!(some_value.unwrap(), 42);
}

/// 测试Result<T, E>类型操作
#[test]
fn test_result_type_operations() {
    let ok_result: Result<i32, &str> = Ok(42);
    let err_result: Result<i32, &str> = Err("error");

    assert!(ok_result.is_ok());
    assert!(err_result.is_err());
    assert_eq!(ok_result.unwrap(), 42);
}

/// 测试切片类型
#[test]
fn test_slice_types() {
    let arr = [1, 2, 3, 4, 5];
    let slice: &[i32] = &arr;

    assert_eq!(slice.len(), 5);
    assert_eq!(slice[0], 1);
    assert_eq!(slice.last(), Some(&5));
}

/// 测试动态类型
#[test]
fn test_dynamic_types() {
    // trait对象动态分发
    trait Greet {
        fn greet(&self) -> String;
    }

    struct Person;
    impl Greet for Person {
        fn greet(&self) -> String {
            String::from("Hello!")
        }
    }

    let person: Box<dyn Greet> = Box::new(Person);
    assert_eq!(person.greet(), "Hello!");
}
