//! 生命周期系统示例代码
//! 
//! 本文件包含了生命周期系统的各种示例，包括：
//! - 生命周期基础
//! - 生命周期注解
//! - 生命周期推断
//! - 高级生命周期特性
//! - 常见模式和最佳实践

/// 生命周期基础示例
pub fn lifetime_basics_examples() {
    println!("=== 生命周期基础示例 ===");
    
    // 基本生命周期
    let x = 5;
    let r = &x;
    println!("r: {}", r);
    
    // 函数中的生命周期
    let string1 = String::from("long string is long");
    {
        let string2 = String::from("xyz");
        let result = longest(string1.as_str(), string2.as_str());
        println!("The longest string is {}", result);
    }
}

/// 生命周期注解示例
pub fn lifetime_annotation_examples() {
    println!("\n=== 生命周期注解示例 ===");
    
    // 结构体中的生命周期
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.').next().expect("Could not find a '.'");
    let i = ImportantExcerpt {
        part: first_sentence,
    };
    
    println!("Excerpt: {}", i.part);
    println!("Level: {}", i.level());
    
    let announcement = "Attention please";
    let part = i.announce_and_return_part(announcement);
    println!("Announced part: {}", part);
}

/// 生命周期推断示例
pub fn lifetime_elision_examples() {
    println!("\n=== 生命周期推断示例 ===");
    
    let s = String::from("hello world");
    let first_word = get_first_word(&s);
    println!("First word: {}", first_word);
    
    let s2 = String::from("rust programming");
    let first_word2 = get_first_word(&s2);
    println!("First word: {}", first_word2);
}

/// 高级生命周期示例
pub fn advanced_lifetimes_examples() {
    println!("\n=== 高级生命周期示例 ===");
    
    // 多重生命周期
    let s1 = "hello";
    let s2 = "world";
    let result = multiple_lifetimes(s1, s2);
    println!("Multiple lifetimes result: {}", result);
    
    // 生命周期约束
    let long = "this is a long string";
    let short = "short";
    let constrained_result = lifetime_constraints(long, short);
    println!("Constrained result: {}", constrained_result);
    
    // 高阶生命周期
    fn truncate_string(s: &str) -> &str {
        if s.len() > 5 {
            &s[..5]
        } else {
            s
        }
    }
    higher_ranked_lifetime(&truncate_string);
}

/// 生命周期与泛型示例
pub fn lifetime_generics_examples() {
    println!("\n=== 生命周期与泛型示例 ===");
    
    let x = 42;
    let y = 100;
    let result = generic_lifetime(&x, &y);
    println!("Generic lifetime result: {}", result);
    
    let string_ref = GenericRef::new("hello");
    let value = string_ref.get();
    println!("Generic ref value: {}", value);
}

/// 生命周期与特征示例
pub fn lifetime_traits_examples() {
    println!("\n=== 生命周期与特征示例 ===");
    
    let processor = StringProcessor;
    let input = "hello world";
    let result = use_processor(processor, input);
    println!("Processor result: {}", result);
    
    // 特征对象生命周期
    let objects: Vec<Box<dyn Drawable>> = vec![
        Box::new(Circle { radius: 5.0 }),
        Box::new(Rectangle { width: 3.0, height: 4.0 }),
    ];
    
    draw_objects(&objects);
}

/// 常见模式示例
pub fn common_patterns_examples() {
    println!("\n=== 常见模式示例 ===");
    
    // 迭代器模式
    let text = "hello world from rust";
    let words = Words::new(text);
    
    println!("Words:");
    for word in words {
        println!("  {}", word);
    }
    
    // 缓存模式
    let mut cache = Cache::new();
    let data = vec![1, 2, 3, 4, 5];
    
    cache.insert("numbers".to_string(), &data);
    
    if let Some(cached) = cache.get("numbers") {
        println!("Cached data: {:?}", cached);
    }
    
    // 解析器模式
    let input = "hello 123 world 456";
    let mut parser = Parser::new(input);
    
    println!("Parsed tokens:");
    while let Some(token) = parser.parse_token() {
        println!("  {:?}", token);
    }
}

/// 性能考虑示例
#[allow(unused_variables)]
pub fn performance_examples() {
    println!("\n=== 性能考虑示例 ===");
    
    // 生命周期对性能的影响
    let data = "hello world";
    let result = no_runtime_cost(data);
    println!("No runtime cost result: {}", result);
    
    // 优化策略
    let s = String::from("hello");
    let result = simple_function(&s);
    println!("Simple function result: {}", result);
    
    // 内存布局
    let s = String::from("hello");
    let r = RefStruct { data: &s };
    println!("RefStruct size: {}", std::mem::size_of::<RefStruct>());
    println!("&str size: {}", std::mem::size_of::<&str>());
}

/// 调试技巧示例
#[allow(unused_variables)]
pub fn debugging_examples() {
    println!("\n=== 调试技巧示例 ===");
    
    // 使用类型注解帮助调试
    let x: i32 = 42;
    let y: i32 = x + 1;
    let z: String = y.to_string();
    println!("Debug values: x={}, y={}, z={}", x, y, z);
    
    // 常见错误模式
    let s = String::from("hello");
    let result = get_first_word(&s);
    println!("First word: {}", result);
    println!("Original string: {}", s);  // 正确：s 仍然有效
}

// ============================================================================
// 辅助函数和结构体定义
// ============================================================================

/// 最长字符串函数
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

/// 重要摘录结构体
struct ImportantExcerpt<'a> {
    part: &'a str,
}

impl<'a> ImportantExcerpt<'a> {
    fn level(&self) -> i32 {
        3
    }
    
    fn announce_and_return_part(&self, announcement: &str) -> &str {
        println!("Attention please: {}", announcement);
        self.part
    }
}

/// 获取第一个单词
fn get_first_word(s: &str) -> &str {
    let bytes = s.as_bytes();
    
    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }
    
    &s[..]
}

/// 多重生命周期函数
#[allow(unused_variables)]
fn multiple_lifetimes<'a, 'b>(x: &'a str, y: &'b str) -> &'a str {
    x
}

/// 生命周期约束函数
#[allow(unused_variables)]
fn lifetime_constraints<'a, 'b>(x: &'a str, y: &'b str) -> &'a str
where
    'b: 'a,
{
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

/// 高阶生命周期约束
#[allow(unused_variables)]
fn higher_ranked_lifetime<F>(f: &F)
where
    F: for<'a> Fn(&'a str) -> &'a str,
{
    let s = "hello world";
    let result = f(s);
    println!("HRTB result: {}", result);
}

/// 泛型生命周期函数
fn generic_lifetime<'a, T>(x: &'a T, y: &'a T) -> &'a T
where
    T: std::fmt::Display,
{
    println!("Comparing: {} and {}", x, y);
    x
}

/// 泛型引用结构体
#[allow(unused_variables)]
struct GenericRef<'a, T: ?Sized> {
    value: &'a T,
}

impl<'a, T: ?Sized> GenericRef<'a, T> {
    fn new(value: &'a T) -> Self {
        GenericRef { value }
    }
    
    fn get(&self) -> &'a T {
        self.value
    }
}

/// 处理器特征
#[allow(unused_variables)]
trait Processor {
    type Output<'a> where Self: 'a;
    fn process<'a>(&self, input: &'a str) -> Self::Output<'a>;
}

/// 字符串处理器
#[allow(unused_variables)]
struct StringProcessor;

impl Processor for StringProcessor {
    type Output<'a> = &'a str;
    
    fn process<'a>(&self, input: &'a str) -> Self::Output<'a> {
        input.trim()
    }
}

/// 使用处理器
#[allow(unused_variables)]
fn use_processor<'a, P>(processor: P, input: &'a str) -> P::Output<'a>
where
    P: Processor,
{
    processor.process(input)
}

/// 可绘制特征
#[allow(dead_code)]
trait Drawable {
    fn draw(&self);
}

/// 圆形
#[allow(dead_code)]
struct Circle {
    radius: f64,
}

impl Drawable for Circle {
    fn draw(&self) {
        println!("Drawing circle with radius {}", self.radius);
    }
}

/// 矩形
#[allow(dead_code)]
struct Rectangle {
    width: f64,
    height: f64,
}

impl Drawable for Rectangle {
    fn draw(&self) {
        println!("Drawing rectangle {}x{}", self.width, self.height);
    }
}

/// 绘制对象
#[allow(dead_code)]
fn draw_objects(objects: &[Box<dyn Drawable>]) {
    for object in objects {
        object.draw();
    }
}

/// 单词迭代器
#[allow(dead_code)]
struct Words<'a> {
    text: &'a str,
    position: usize,
}

impl<'a> Words<'a> {
    fn new(text: &'a str) -> Self {
        Words { text, position: 0 }
    }
}

impl<'a> Iterator for Words<'a> {
    type Item = &'a str;
    
    fn next(&mut self) -> Option<Self::Item> {
        let text = &self.text[self.position..];
        
        for (i, c) in text.char_indices() {
            if c.is_whitespace() {
                if i > 0 {
                    let word = &text[..i];
                    self.position += i + 1;
                    return Some(word);
                }
                self.position += 1;
            }
        }
        
        if text.is_empty() {
            None
        } else {
            self.position = self.text.len();
            Some(text)
        }
    }
}

/// 缓存结构
#[allow(dead_code)]
struct Cache<'a, T> {
    data: std::collections::HashMap<String, &'a T>,
}

impl<'a, T> Cache<'a, T> {
    fn new() -> Self {
        Cache {
            data: std::collections::HashMap::new(),
        }
    }
    
    fn get(&self, key: &str) -> Option<&'a T> {
        self.data.get(key).copied()
    }
    
    fn insert(&mut self, key: String, value: &'a T) {
        self.data.insert(key, value);
    }
}

/// 解析器
#[allow(dead_code)]
struct Parser<'a> {
    input: &'a str,
    position: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Parser { input, position: 0 }
    }
    
    fn parse_token(&mut self) -> Option<Token<'a>> {
        self.skip_whitespace();
        
        if self.position >= self.input.len() {
            return None;
        }
        
        let start = self.position;
        
        if self.peek().unwrap().is_ascii_alphabetic() {
            self.parse_word()
        } else if self.peek().unwrap().is_ascii_digit() {
            self.parse_number()
        } else {
            self.consume();
            Some(Token::Other(&self.input[start..self.position]))
        }
    }
    
    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_whitespace() {
                self.consume();
            } else {
                break;
            }
        }
    }
    
    fn parse_word(&mut self) -> Option<Token<'a>> {
        let start = self.position;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_alphabetic() {
                self.consume();
            } else {
                break;
            }
        }
        Some(Token::Word(&self.input[start..self.position]))
    }
    
    fn parse_number(&mut self) -> Option<Token<'a>> {
        let start = self.position;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                self.consume();
            } else {
                break;
            }
        }
        Some(Token::Number(&self.input[start..self.position]))
    }
    
    fn peek(&self) -> Option<char> {
        self.input[self.position..].chars().next()
    }
    
    fn consume(&mut self) -> Option<char> {
        let ch = self.peek()?;
        self.position += ch.len_utf8();
        Some(ch)
    }
}

/// 令牌类型
#[allow(dead_code)]
#[allow(unused_variables)]
#[derive(Debug)]
enum Token<'a> {
    Word(&'a str),
    Number(&'a str),
    Other(&'a str),
}

/// 性能示例函数
#[allow(unused_variables)]
fn no_runtime_cost<'a>(x: &'a str) -> &'a str {
    x
}

#[allow(dead_code)]
fn simple_function(s: &str) -> &str {
    s
}

/// 引用结构体
#[allow(dead_code)]
#[allow(unused_variables)]
struct RefStruct<'a> {
    data: &'a str,
}

/// 运行所有生命周期示例
pub fn run_all_examples() {
    println!("Rust 生命周期系统示例");
    println!("======================");
    
    lifetime_basics_examples();
    lifetime_annotation_examples();
    lifetime_elision_examples();
    advanced_lifetimes_examples();
    lifetime_generics_examples();
    lifetime_traits_examples();
    common_patterns_examples();
    performance_examples();
    debugging_examples();
    
    println!("\n所有示例运行完成！");
}