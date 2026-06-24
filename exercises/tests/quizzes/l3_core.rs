//! L3 核心概念嵌入式测验（quizzes/l3_core）
//!
//! 覆盖范围：
//! - 基础 6 题：所有权、借用、生命周期
//! - 进阶 6 题：trait、泛型、错误处理
//!
//! 运行: cargo test --test quizzes

// ========== 基础：所有权、借用、生命周期 ==========

/// 测验 1：所有权移动与 `clone`
#[test]
fn test_ownership_move_and_clone() {
    let s1 = String::from("hello");
    let s2 = s1.clone();

    // clone 后原值仍可用
    assert_eq!(s1, "hello");
    assert_eq!(s2, "hello");
}

/// 测验 2：可变借用的独占性
#[test]
fn test_mutable_borrow_exclusive() {
    let mut x = 5;
    let r = &mut x;
    *r += 1;

    assert_eq!(*r, 6);
}

/// 测验 3：不可变借用允许多个读者
#[test]
fn test_shared_borrow_multiple_readers() {
    let x = 10;
    let r1 = &x;
    let r2 = &x;

    assert_eq!(*r1 + *r2, 20);
}

/// 测验 4：函数返回引用时生命周期省略规则
#[test]
fn test_lifetime_elision_returns_input_reference() {
    fn first(s: &[i32]) -> &i32 {
        &s[0]
    }

    let v = vec![1, 2, 3];
    assert_eq!(*first(&v), 1);
}

/// 测验 5：带引用的结构体需要显式生命周期
#[test]
fn test_struct_with_reference_lifetime() {
    struct Wrapper<'a> {
        value: &'a str,
    }

    let s = String::from("rust");
    let w = Wrapper { value: &s };

    assert_eq!(w.value, "rust");
}

/// 测验 6：切片引用的生命周期受输入绑定
#[test]
fn test_slice_lifetime_bound() {
    fn max_slice(s: &[i32]) -> Option<&i32> {
        s.iter().max()
    }

    let v = vec![3, 1, 4, 1, 5];
    assert_eq!(*max_slice(&v).unwrap(), 5);
}

// ========== 进阶：trait、泛型、错误处理 ==========

/// 测验 7：泛型函数与 trait bound
#[test]
fn test_generic_trait_bound() {
    fn double<T>(x: T) -> T
    where
        T: std::ops::Add<Output = T> + Copy,
    {
        x + x
    }

    assert_eq!(double(3), 6);
    assert_eq!(double(2.5), 5.0);
}

/// 测验 8：trait object `dyn Trait`
#[test]
fn test_trait_object_dyn() {
    trait Greet {
        fn greet(&self) -> &'static str;
    }

    struct Cat;
    impl Greet for Cat {
        fn greet(&self) -> &'static str {
            "meow"
        }
    }

    fn say_hi(g: &dyn Greet) -> &'static str {
        g.greet()
    }

    let cat = Cat;
    assert_eq!(say_hi(&cat), "meow");
}

/// 测验 9：关联类型
#[test]
fn test_associated_types() {
    trait StepByOne {
        type Item;
        fn next(&mut self) -> Option<Self::Item>;
    }

    struct Counter(u32);
    impl StepByOne for Counter {
        type Item = u32;
        fn next(&mut self) -> Option<Self::Item> {
            self.0 += 1;
            Some(self.0)
        }
    }

    let mut c = Counter(0);
    assert_eq!(c.next(), Some(1));
    assert_eq!(c.next(), Some(2));
}

/// 测验 10：`Result` 组合子与 `?` 运算符
#[test]
fn test_result_combinators() {
    fn parse_add(a: &str, b: &str) -> Result<i32, std::num::ParseIntError> {
        Ok(a.parse::<i32>()? + b.parse::<i32>()?)
    }

    assert_eq!(parse_add("2", "3").unwrap(), 5);
    assert!(parse_add("x", "3").is_err());
}

/// 测验 11：自定义错误类型
#[test]
fn test_custom_error_type() {
    use std::fmt;

    #[derive(Debug)]
    enum ValidationError {
        Empty,
        TooLong,
    }

    impl fmt::Display for ValidationError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                ValidationError::Empty => write!(f, "input is empty"),
                ValidationError::TooLong => write!(f, "input is too long"),
            }
        }
    }

    impl std::error::Error for ValidationError {}

    fn validate(s: &str) -> Result<(), ValidationError> {
        if s.is_empty() {
            Err(ValidationError::Empty)
        } else if s.len() > 10 {
            Err(ValidationError::TooLong)
        } else {
            Ok(())
        }
    }

    assert!(validate("").is_err());
    assert!(validate("short").is_ok());
    assert!(validate("this is way too long").is_err());
}

/// 测验 12：Iterator adapter 链
#[test]
fn test_iterator_adapters() {
    let evens_squared: Vec<i32> = (1..=10).filter(|x| x % 2 == 0).map(|x| x * x).collect();

    assert_eq!(evens_squared, vec![4, 16, 36, 64, 100]);
}
