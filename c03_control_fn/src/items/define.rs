/*
在 Rust 中，项是程序的基本构建块，
包括函数、结构体、枚举、模块等。
    
**项可以被视为范畴中的对象，它们定义了程序的结构和行为。**

*/


#[allow(unused)]
// 函数定义
pub fn test_fn() {
    let x = 5;
    println!("x is {}", x);
}

#[allow(unused)]
// 结构体定义
pub struct TestStruct {
    x: i32,
    y: i32,
}


// 枚举定义
pub enum TestEnum {
    X(i32),
    Y(i32),
}


// 模块定义
pub mod test_module {
    pub fn test_fn() {
        println!("test_fn");
    }
}

// 常量定义
pub const TEST_CONST: i32 = 10;

// 静态变量定义
pub static TEST_STATIC: i32 = 20;


// 类型定义
pub type TestType = i32;

// 别名定义
pub type TestAlias = i32;


#[allow(unused)]
// 宏定义
macro_rules! test_macro {
    ($x:expr) => {
        println!("x is {}", $x);
    };
}

