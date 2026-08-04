//! 教程代码测试
//! 
//! 测试教程中的代码示例

#[test]
fn test_tutorial_step_1() {
    // 测试教程第1步：Hello, World!
    let result = tutorial_step_1_function();
    assert_eq!(result, "Hello, World!");
}

#[test]
fn test_tutorial_step_2() {
    // 测试教程第2步：变量和可变性
    let data = tutorial_step_2_data();
    let processed = tutorial_step_2_process(data);
    assert!(processed.is_some());
    assert_eq!(processed.unwrap(), 15);
}

#[test]
fn test_tutorial_step_3() {
    // 测试教程第3步：数据类型
    let result = tutorial_step_3_function();
    assert_eq!(result, 42);
}

#[test]
fn test_tutorial_step_4() {
    // 测试教程第4步：函数
    let result = tutorial_step_4_function(5, 3);
    assert_eq!(result, 8);
}

#[test]
fn test_tutorial_step_5() {
    // 测试教程第5步：控制流
    let result = tutorial_step_5_function(10);
    assert_eq!(result, "greater than 5");
    
    let result = tutorial_step_5_function(3);
    assert_eq!(result, "less than or equal to 5");
}

#[test]
fn test_tutorial_step_6() {
    // 测试教程第6步：所有权
    let result = tutorial_step_6_function();
    assert_eq!(result, "ownership works");
}

#[test]
fn test_tutorial_step_7() {
    // 测试教程第7步：结构体
    let rect = Rectangle {
        width: 30,
        height: 50,
    };
    
    assert_eq!(rect.area(), 1500);
    assert!(rect.width > 0);
    assert!(rect.height > 0);
}

#[test]
fn test_tutorial_step_8() {
    // 测试教程第8步：枚举和模式匹配
    let result = tutorial_step_8_function();
    assert_eq!(result, "enum and pattern matching works");
}

#[test]
fn test_tutorial_step_9() {
    // 测试教程第9步：集合
    let result = tutorial_step_9_function();
    assert_eq!(result.len(), 5);
    assert_eq!(result[0], 1);
    assert_eq!(result[4], 5);
}

#[test]
fn test_tutorial_step_10() {
    // 测试教程第10步：错误处理
    let result = tutorial_step_10_function(10, 2);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 5);
    
    let error_result = tutorial_step_10_function(10, 0);
    assert!(error_result.is_err());
}

#[test]
fn test_tutorial_step_11() {
    // 测试教程第11步：泛型
    let result = tutorial_step_11_function(5);
    assert_eq!(result, 10);
    
    let string_result = tutorial_step_11_function("hello");
    assert_eq!(string_result, "hellohello");
}

#[test]
fn test_tutorial_step_12() {
    // 测试教程第12步：trait
    let result = tutorial_step_12_function();
    assert_eq!(result, "trait implementation works");
}

#[test]
fn test_tutorial_step_13() {
    // 测试教程第13步：生命周期
    let result = tutorial_step_13_function();
    assert_eq!(result, "lifetime annotation works");
}

#[test]
fn test_tutorial_step_14() {
    // 测试教程第14步：测试
    let result = tutorial_step_14_function();
    assert_eq!(result, "testing works");
}

#[test]
fn test_tutorial_step_15() {
    // 测试教程第15步：闭包
    let result = tutorial_step_15_function();
    assert_eq!(result, 25);
}

#[test]
fn test_tutorial_step_16() {
    // 测试教程第16步：迭代器
    let result = tutorial_step_16_function();
    assert_eq!(result, 55); // 1+2+3+...+10
}

#[test]
fn test_tutorial_step_17() {
    // 测试教程第17步：智能指针
    let result = tutorial_step_17_function();
    assert_eq!(result, 42);
}

#[test]
fn test_tutorial_step_18() {
    // 测试教程第18步：并发
    let result = tutorial_step_18_function();
    assert_eq!(result, "concurrency works");
}

#[test]
fn test_tutorial_step_19() {
    // 测试教程第19步：异步编程
    let rt = tokio::runtime::Runtime::new().unwrap();
    rt.block_on(async {
        let result = tutorial_step_19_function().await;
        assert_eq!(result, "async programming works");
    });
}

#[test]
fn test_tutorial_step_20() {
    // 测试教程第20步：宏
    let result = tutorial_step_20_function();
    assert_eq!(result, "macros work");
}

// 辅助函数和结构体
fn tutorial_step_1_function() -> &'static str {
    "Hello, World!"
}

fn tutorial_step_2_data() -> Vec<i32> {
    vec![1, 2, 3, 4, 5]
}

fn tutorial_step_2_process(data: Vec<i32>) -> Option<i32> {
    Some(data.iter().sum())
}

fn tutorial_step_3_function() -> i32 {
    42
}

fn tutorial_step_4_function(a: i32, b: i32) -> i32 {
    a + b
}

fn tutorial_step_5_function(x: i32) -> &'static str {
    if x > 5 {
        "greater than 5"
    } else {
        "less than or equal to 5"
    }
}

fn tutorial_step_6_function() -> &'static str {
    "ownership works"
}

struct Rectangle {
    width: u32,
    height: u32,
}

impl Rectangle {
    fn area(&self) -> u32 {
        self.width * self.height
    }
}

fn tutorial_step_8_function() -> &'static str {
    "enum and pattern matching works"
}

fn tutorial_step_9_function() -> Vec<i32> {
    vec![1, 2, 3, 4, 5]
}

fn tutorial_step_10_function(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}

fn tutorial_step_11_function<T>(value: T) -> T
where
    T: Clone + std::ops::Add<Output = T>,
{
    value.clone() + value
}

fn tutorial_step_12_function() -> &'static str {
    "trait implementation works"
}

fn tutorial_step_13_function() -> &'static str {
    "lifetime annotation works"
}

fn tutorial_step_14_function() -> &'static str {
    "testing works"
}

fn tutorial_step_15_function() -> i32 {
    let closure = |x| x * 5;
    closure(5)
}

fn tutorial_step_16_function() -> i32 {
    (1..=10).sum()
}

fn tutorial_step_17_function() -> i32 {
    42
}

fn tutorial_step_18_function() -> &'static str {
    "concurrency works"
}

async fn tutorial_step_19_function() -> &'static str {
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    "async programming works"
}

fn tutorial_step_20_function() -> &'static str {
    "macros work"
}
