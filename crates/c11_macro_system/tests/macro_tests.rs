//! 宏系统测试套件

#[test]
fn test_declarative_macro() {
    // 测试声明宏的基本功能
    macro_rules! add {
        ($a:expr, $b:expr) => {
            $a + $b
        };
    }
    
    assert_eq!(add!(1, 2), 3);
    assert_eq!(add!(10, 20), 30);
}

#[test]
fn test_vec_macro() {
    // 测试 vec! 宏
    let v = vec![1, 2, 3, 4, 5];
    assert_eq!(v.len(), 5);
    assert_eq!(v[0], 1);
    assert_eq!(v[4], 5);
}

#[test]
fn test_format_macro() {
    // 测试 format! 宏
    let s = format!("Hello, {}!", "World");
    assert_eq!(s, "Hello, World!");
    
    let s2 = format!("Value: {}", 42);
    assert_eq!(s2, "Value: 42");
}

#[test]
fn test_println_macro() {
    // 测试 println! 宏（不会失败，只是确保可以编译）
    println!("Test message");
    println!("Value: {}", 42);
    assert!(true); // 确保测试通过
}

#[test]
fn test_assert_macro() {
    // 测试 assert! 宏
    assert!(true);
    assert!(1 + 1 == 2);
    assert!(10 > 5);
}

#[test]
fn test_option_macro() {
    // 测试 Option 相关宏
    let some = Some(42);
    let none: Option<i32> = None;
    
    assert_eq!(some, Some(42));
    assert_eq!(none, None);
}

#[test]
fn test_result_macro() {
    // 测试 Result 相关宏
    let ok: Result<i32, &str> = Ok(42);
    let err: Result<i32, &str> = Err("error");
    
    assert_eq!(ok, Ok(42));
    assert_eq!(err, Err("error"));
}

#[test]
fn test_custom_macro() {
    // 测试自定义宏
    macro_rules! my_vec {
        ($($x:expr),*) => {
            {
                let mut temp_vec = Vec::new();
                $(
                    temp_vec.push($x);
                )*
                temp_vec
            }
        };
    }
    
    let v = my_vec![1, 2, 3];
    assert_eq!(v, vec![1, 2, 3]);
}

#[test]
fn test_macro_repetition() {
    // 测试宏重复
    macro_rules! repeat {
        ($x:expr; $n:expr) => {
            {
                let mut v = Vec::new();
                for _ in 0..$n {
                    v.push($x);
                }
                v
            }
        };
    }
    
    let v = repeat!(42; 5);
    assert_eq!(v, vec![42, 42, 42, 42, 42]);
}

#[test]
fn test_macro_hygiene() {
    // 测试宏卫生性
    macro_rules! test_hygiene {
        ($x:expr) => {
            {
                let temp = $x;
                temp
            }
        };
    }
    
    let value = 42;
    let result = test_hygiene!(value + 1);
    assert_eq!(result, 43);
    assert_eq!(value, 42); // 原始值不应改变
}
