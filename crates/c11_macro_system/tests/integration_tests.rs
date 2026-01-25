//! 宏系统模块集成测试套件 / Macro System Module Integration Test Suite

/// 测试声明宏集成
#[test]
fn test_declarative_macro_integration() {
    macro_rules! add {
        ($a:expr, $b:expr) => {
            $a + $b
        };
    }
    
    assert_eq!(add!(3, 4), 7);
    assert_eq!(add!(1.5, 2.5), 4.0);
}

/// 测试宏重复集成
#[test]
fn test_macro_repetition_integration() {
    macro_rules! vec {
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
    
    let v = vec![1, 2, 3];
    assert_eq!(v, vec![1, 2, 3]);
}

/// 测试宏模式匹配集成
#[test]
fn test_macro_pattern_matching_integration() {
    macro_rules! test_match {
        (one) => { 1 };
        (two) => { 2 };
        (three) => { 3 };
        ($other:expr) => { 0 };
    }
    
    assert_eq!(test_match!(one), 1);
    assert_eq!(test_match!(two), 2);
    assert_eq!(test_match!(three), 3);
    assert_eq!(test_match!(four), 0);
}

/// 测试递归宏集成
#[test]
fn test_recursive_macro_integration() {
    macro_rules! factorial {
        (0) => { 1 };
        ($n:expr) => {
            $n * factorial!($n - 1)
        };
    }
    
    assert_eq!(factorial!(0), 1);
    assert_eq!(factorial!(5), 120);
}

/// 测试宏元编程集成
#[test]
fn test_metaprogramming_integration() {
    macro_rules! create_struct {
        ($name:ident { $($field:ident: $type:ty),* }) => {
            struct $name {
                $(
                    $field: $type,
                )*
            }
        };
    }
    
    create_struct!(Person {
        name: String,
        age: u32
    });
    
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
    };
    
    assert_eq!(person.name, "Alice");
    assert_eq!(person.age, 30);
}

/// 测试宏代码生成集成
#[test]
fn test_code_generation_integration() {
    macro_rules! generate_getters {
        ($struct_name:ident { $($field:ident: $type:ty),* }) => {
            impl $struct_name {
                $(
                    fn $field(&self) -> &$type {
                        &self.$field
                    }
                )*
            }
        };
    }
    
    struct Data {
        value: i32,
        name: String,
    }
    
    generate_getters!(Data {
        value: i32,
        name: String
    });
    
    let data = Data {
        value: 42,
        name: "test".to_string(),
    };
    
    assert_eq!(*data.value(), 42);
    assert_eq!(*data.name(), "test");
}
