//! 示例代码测试
//! 
//! 测试文档中的示例代码是否可运行

#[test]
fn test_ownership_examples() {
    // 测试所有权示例
    let s = String::from("hello");
    let len = calculate_length(&s);
    assert_eq!(len, 5);
    assert_eq!(s, "hello"); // s 仍然可用
}

#[test]
fn test_borrowing_examples() {
    // 测试借用示例
    let mut s = String::from("hello");
    change(&mut s);
    assert_eq!(s, "hello, world");
}

#[test]
fn test_lifetime_examples() {
    // 测试生命周期示例
    let string1 = String::from("long string is long");
    let result;
    {
        let string2 = String::from("xyz");
        result = longest(&string1, &string2);
    }
    assert_eq!(result, "long string is long");
}

#[test]
fn test_generic_examples() {
    // 测试泛型示例
    let number_list = vec![34, 50, 25, 100, 65];
    let result = largest(&number_list);
    assert_eq!(result, Some(&100));
    
    let char_list = vec!['y', 'm', 'a', 'q'];
    let result = largest(&char_list);
    assert_eq!(result, Some(&'y'));
}

#[test]
fn test_trait_examples() {
    // 测试trait示例
    let tweet = Tweet {
        username: String::from("horse_ebooks"),
        content: String::from("of course, as you probably already know, people"),
        reply: false,
        retweet: false,
    };
    
    assert_eq!(tweet.summarize(), "horse_ebooks: of course, as you probably already know, people");
}

#[test]
fn test_error_handling_examples() {
    // 测试错误处理示例
    let result = divide(10, 2);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 5);
    
    let result = divide(10, 0);
    assert!(result.is_err());
}

#[test]
fn test_collection_examples() {
    // 测试集合示例
    let mut v = vec![1, 2, 3, 4, 5];
    let first = &v[0];
    v.push(6);
    // 注意：这里不能使用 first，因为 v.push(6) 可能导致重新分配
    
    let third: &i32 = &v[2];
    assert_eq!(*third, 3);
}

#[test]
fn test_string_examples() {
    // 测试字符串示例
    let s1 = String::from("Hello, ");
    let s2 = String::from("world!");
    let s3 = s1 + &s2; // s1 被移动了
    assert_eq!(s3, "Hello, world!");
}

#[test]
fn test_hashmap_examples() {
    // 测试HashMap示例
    use std::collections::HashMap;
    
    let mut scores = HashMap::new();
    scores.insert(String::from("Blue"), 10);
    scores.insert(String::from("Yellow"), 50);
    
    let team_name = String::from("Blue");
    let score = scores.get(&team_name);
    assert_eq!(score, Some(&10));
}

#[test]
fn test_iteration_examples() {
    // 测试迭代器示例
    let v1 = vec![1, 2, 3];
    let v1_iter = v1.iter();
    let total: i32 = v1_iter.sum();
    assert_eq!(total, 6);
    
    let v2: Vec<_> = v1.iter().map(|x| x + 1).collect();
    assert_eq!(v2, vec![2, 3, 4]);
}

#[test]
fn test_closure_examples() {
    // 测试闭包示例
    let expensive_closure = |num| {
        println!("calculating slowly...");
        num
    };
    
    let result = expensive_closure(5);
    assert_eq!(result, 5);
}

#[test]
fn test_async_examples() {
    // 测试异步示例
    let rt = tokio::runtime::Runtime::new().unwrap();
    rt.block_on(async {
        let result = async_example().await;
        assert!(result.is_ok());
    });
}

// 辅助函数和结构体
fn calculate_length(s: &String) -> usize {
    s.len()
}

fn change(s: &mut String) {
    s.push_str(", world");
}

fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

fn largest<T>(list: &[T]) -> Option<&T>
where
    T: PartialOrd,
{
    let mut largest = list.get(0)?;
    
    for item in list {
        if item > largest {
            largest = item;
        }
    }
    
    Some(largest)
}

pub struct Tweet {
    pub username: String,
    pub content: String,
    pub reply: bool,
    pub retweet: bool,
}

impl Summary for Tweet {
    fn summarize(&self) -> String {
        format!("{}: {}", self.username, self.content)
    }
}

pub trait Summary {
    fn summarize(&self) -> String {
        String::from("(Read more...)")
    }
}

fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}

async fn async_example() -> Result<(), String> {
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    Ok(())
}
