//! 泛型和边界测试
//!
//! 测试Rust的泛型系统和类型边界：
//! - 基本泛型
//! - 泛型约束
//! - where子句
//! - 生命周期边界

/// 测试基本泛型函数
#[test]
fn test_basic_generic_function() {
    fn identity<T>(x: T) -> T {
        x
    }
    
    assert_eq!(identity(42), 42);
    assert_eq!(identity("hello"), "hello");
    assert_eq!(identity(vec![1, 2, 3]), vec![1, 2, 3]);
}

/// 测试泛型结构体
#[test]
fn test_generic_struct() {
    struct Point<T> {
        x: T,
        y: T,
    }
    
    impl<T> Point<T> {
        fn new(x: T, y: T) -> Self {
            Point { x, y }
        }
        
        fn x(&self) -> &T {
            &self.x
        }
    }
    
    let int_point = Point::new(1, 2);
    assert_eq!(*int_point.x(), 1);
    
    let float_point = Point::new(1.0, 2.0);
    assert_eq!(*float_point.x(), 1.0);
}

/// 测试多泛型参数
#[test]
fn test_multiple_generic_params() {
    struct Pair<T, U> {
        first: T,
        second: U,
    }
    
    let pair = Pair {
        first: 1,
        second: "one",
    };
    
    assert_eq!(pair.first, 1);
    assert_eq!(pair.second, "one");
}

/// 测试泛型枚举
#[test]
fn test_generic_enum() {
    enum Result<T, E> {
        Ok(T),
        Err(E),
    }
    
    let success: Result<i32, &str> = Result::Ok(42);
    let failure: Result<i32, &str> = Result::Err("error");
    
    match success {
        Result::Ok(v) => assert_eq!(v, 42),
        Result::Err(_) => panic!("Expected Ok"),
    }
}

/// 测试泛型边界（Trait Bounds）
#[test]
fn test_trait_bounds() {
    use std::fmt::Display;
    
    fn print_item<T: Display>(item: T) {
        println!("{}", item);
    }
    
    print_item(42);
    print_item("hello");
}

/// 测试多重边界
#[test]
fn test_multiple_bounds() {
    use std::fmt::Debug;
    
    fn compare_and_print<T: PartialEq + Debug>(a: T, b: T) {
        if a == b {
            println!("{:?} equals {:?}", a, b);
        } else {
            println!("{:?} not equals {:?}", a, b);
        }
    }
    
    compare_and_print(1, 1);
    compare_and_print(1, 2);
}

/// 测试where子句
#[test]
fn test_where_clause() {
    fn some_function<T, U>(t: T, u: U) -> i32
    where
        T: Clone + std::fmt::Debug,
        U: Clone + PartialEq,
    {
        let _t2 = t.clone();
        let u2 = u.clone();
        
        if u == u2 {
            1
        } else {
            0
        }
    }
    
    assert_eq!(some_function(1, 2), 1);
}

/// 测试默认泛型类型
#[test]
fn test_default_generic_type() {
    trait Add<Rhs = Self> {
        type Output;
        fn add(self, rhs: Rhs) -> Self::Output;
    }
    
    #[derive(Debug, PartialEq)]
    struct Millimeters(u32);
    #[derive(Debug, PartialEq)]
    struct Meters(u32);
    
    impl Add for Millimeters {
        type Output = Millimeters;
        fn add(self, other: Millimeters) -> Millimeters {
            Millimeters(self.0 + other.0)
        }
    }
    
    impl Add<Meters> for Millimeters {
        type Output = Millimeters;
        fn add(self, other: Meters) -> Millimeters {
            Millimeters(self.0 + (other.0 * 1000))
        }
    }
    
    let m1 = Millimeters(100);
    let m2 = Millimeters(200);
    assert_eq!(m1.add(m2), Millimeters(300));
}

/// 测试泛型方法
#[test]
fn test_generic_methods() {
    struct Container<T> {
        value: T,
    }
    
    impl<T> Container<T> {
        fn new(value: T) -> Self {
            Container { value }
        }
        
        fn get(&self) -> &T {
            &self.value
        }
        
        fn set(&mut self, value: T) {
            self.value = value;
        }
    }
    
    let mut container = Container::new(42);
    assert_eq!(*container.get(), 42);
    
    container.set(100);
    assert_eq!(*container.get(), 100);
}

/// 测试常量泛型
#[test]
fn test_const_generics() {
    struct Array<T, const N: usize> {
        data: [T; N],
    }
    
    impl<T: Default + Copy, const N: usize> Array<T, N> {
        fn new() -> Self {
            Array {
                data: [T::default(); N],
            }
        }
        
        fn len(&self) -> usize {
            N
        }
    }
    
    let arr: Array<i32, 5> = Array::new();
    assert_eq!(arr.len(), 5);
}

/// 测试泛型与生命周期结合
#[test]
fn test_generic_with_lifetimes() {
    struct Ref<'a, T: 'a> {
        value: &'a T,
    }
    
    impl<'a, T> Ref<'a, T> {
        fn new(value: &'a T) -> Self {
            Ref { value }
        }
        
        fn get(&self) -> &'a T {
            self.value
        }
    }
    
    let x = 42;
    let ref_x = Ref::new(&x);
    assert_eq!(*ref_x.get(), 42);
}

/// 测试关联类型的泛型实现
#[test]
fn test_associated_types_with_generics() {
    trait Container {
        type Item;
        fn get(&self) -> &Self::Item;
    }
    
    struct Wrapper<T> {
        value: T,
    }
    
    impl<T> Container for Wrapper<T> {
        type Item = T;
        fn get(&self) -> &T {
            &self.value
        }
    }
    
    let wrapper = Wrapper { value: "hello" };
    assert_eq!(*wrapper.get(), "hello");
}
