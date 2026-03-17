//! 现代 Rust 模式 (2024-2025)
//!
//! 本示例展示 Rust 1.70+ 到 1.94 的现代编程模式：
//! - let...else 语法
//! - ControlFlow 类型
//! - 内联 const
//! - 泛型关联类型 (GATs)
//! - RPITIT (Return Position Impl Trait In Traits)
//! - 异步 trait
//! - 类型推导改进

#![allow(unused)]

use std::collections::HashMap;
use std::fmt::Display;
use std::ops::ControlFlow;
use std::ops::Deref;

/// # 1. let...else 语法 (Rust 1.65+)
///
/// 用于提前返回的模式匹配，比 match 更简洁
mod let_else_patterns {
    use std::collections::HashMap;
    /// 解析配置的传统方式
    pub fn parse_config_legacy(input: &str) -> Option<HashMap<String, String>> {
        let lines: Vec<&str> = match input.lines().next() {
            Some(first) if first.starts_with("#CONFIG") => input.lines().skip(1).collect(),
            _ => return None,
        };

        let mut config = HashMap::new();
        for line in lines {
            let parts: Vec<&str> = line.splitn(2, '=').collect();
            if parts.len() != 2 {
                continue;
            }
            config.insert(parts[0].to_string(), parts[1].to_string());
        }
        Some(config)
    }

    /// 使用 let...else 的现代方式
    pub fn parse_config_modern(input: &str) -> Option<HashMap<String, String>> {
        // 提前返回无效输入
        let Some(first) = input.lines().next() else {
            return None;
        };
        let true = first.starts_with("#CONFIG") else {
            return None;
        };

        let mut config = HashMap::new();
        for line in input.lines().skip(1) {
            // 优雅地解构
            let Some((key, value)) = line.split_once('=') else {
                continue;
            };
            config.insert(key.to_string(), value.to_string());
        }
        Some(config)
    }

    /// 更复杂的 let...else 用法
    pub fn process_nested_data(data: Option<Option<Option<String>>>) -> String {
        let Some(Some(Some(content))) = data else {
            return "default".to_string();
        };
        content.to_uppercase()
    }

    pub fn demonstrate() {
        println!("=== let...else 语法 ===\n");

        let config_str = "#CONFIG\nname=MyApp\nversion=1.0.0\nauthor=Alice";

        match parse_config_modern(config_str) {
            Some(cfg) => println!("Parsed config: {:?}", cfg),
            None => println!("Failed to parse"),
        }

        let nested = Some(Some(Some("hello".to_string())));
        println!("Nested result: {}", process_nested_data(nested));

        println!();
    }
}

/// # 2. ControlFlow 类型 (Rust 1.55+)
///
/// 用于自定义控制流的优雅抽象
mod control_flow_patterns {
    use super::*;
    use std::collections::HashMap;

    /// 使用 ControlFlow 实现提前终止的遍历
    pub fn find_first_error<T, E>(
        items: &[T],
        validator: impl Fn(&T) -> Result<(), E>,
    ) -> Result<(), E> {
        for item in items {
            validator(item)?;
        }
        Ok(())
    }

    /// 使用 ControlFlow 实现有限搜索
    pub fn find_with_limit<T>(
        items: &[T],
        limit: usize,
        predicate: impl Fn(&T) -> bool,
    ) -> Option<&T> {
        for (idx, item) in items.iter().enumerate() {
            if idx >= limit {
                return None;
            }
            if predicate(item) {
                return Some(item);
            }
        }
        None
    }

    /// 批量处理的 ControlFlow
    pub fn process_batch<T, E>(
        items: Vec<T>,
        processor: impl Fn(T) -> Result<T, E>,
    ) -> Result<Vec<T>, E> {
        let mut results = Vec::with_capacity(items.len());

        for item in items {
            match processor(item) {
                Ok(processed) => results.push(processed),
                Err(e) => return Err(e),
            }
        }

        Ok(results)
    }

    pub fn demonstrate() {
        println!("=== ControlFlow 类型 ===\n");

        let numbers = vec![1, 2, 3, 4, 5];

        // 查找第一个偶数，最多检查前3个
        if let Some(n) = find_with_limit(&numbers, 3, |&x| x % 2 == 0) {
            println!("Found even number within limit: {}", n);
        }

        // 批量处理
        let doubled: Result<Vec<i32>, ()> = process_batch(vec![1, 2, 3, 4, 5], |x| Ok(x * 2));
        println!("Doubled: {:?}", doubled);

        println!();
    }
}

/// # 3. 内联 const (Rust 1.79+)
///
/// 编译期常量计算
mod inline_const {
    /// 编译时计算数组大小
    pub const fn array_size() -> usize {
        1024 * 1024 // 1MB
    }

    /// 编译时计算哈希
    pub const fn hash_string(s: &str) -> u64 {
        let mut hash = 0u64;
        let bytes = s.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            hash = hash.wrapping_mul(31).wrapping_add(bytes[i] as u64);
            i += 1;
        }
        hash
    }

    pub fn demonstrate() {
        println!("=== 内联 const ===\n");

        // 使用编译期常量
        const BUFFER_SIZE: usize = array_size();
        let _buffer = vec![0u8; BUFFER_SIZE];

        // 编译时计算的哈希
        const HASH: u64 = hash_string("hello");
        println!("Compile-time hash: {}", HASH);

        println!("Buffer size: {} bytes", BUFFER_SIZE);
        println!();
    }
}

/// # 4. 泛型关联类型 (GATs) - Rust 1.65+
///
/// 允许 trait 中的关联类型带有泛型参数
mod gat_patterns {
    use std::collections::HashMap;
    
    /// 泛型集合 trait
    pub trait Container {
        type Item<'a>
        where
            Self: 'a;

        fn get<'a>(&'a self, index: usize) -> Option<Self::Item<'a>>;
    }

    impl<T> Container for Vec<T> {
        type Item<'a> = &'a T where T: 'a;

        fn get<'a>(&'a self, index: usize) -> Option<&'a T> {
            if index < self.len() {
                Some(&self[index])
            } else {
                None
            }
        }
    }

    impl<K, V> Container for HashMap<K, V> {
        type Item<'a> = (&'a K, &'a V) where K: 'a, V: 'a;

        fn get<'a>(&'a self, _index: usize) -> Option<Self::Item<'a>> {
            self.iter().nth(_index)
        }
    }

    /// 异步迭代器 trait（使用 GAT）
    pub trait AsyncIterator {
        type Item<'a>
        where
            Self: 'a;

        async fn next(&mut self) -> Option<Self::Item<'_>>;
    }

    pub fn demonstrate() {
        println!("=== 泛型关联类型 (GATs) ===\n");

        let vec = vec![1, 2, 3, 4, 5];
        let _item: Option<&i32> = vec.get(0);

        let map: HashMap<String, i32> =
            [("a".to_string(), 1), ("b".to_string(), 2)]
                .into_iter()
                .collect();
        // 使用 Container trait 的 get 方法
        let _entry: Option<(&String, &i32)> = Container::get(&map, 0);

        println!("GATs enable generic container abstractions");
        println!();
    }
}

/// # 5. 特质中的返回位置 impl Trait (RPITIT) - Rust 1.75+
///
/// 在 trait 方法中使用 impl Trait 作为返回类型
mod rpitit_patterns {
    use std::fmt::Display;

    /// 传统方式：需要显式关联类型
    pub trait ProducerOld {
        type Output: Display;
        fn produce(&self) -> Self::Output;
    }

    /// 现代方式：使用 impl Trait
    pub trait Producer {
        fn produce(&self) -> impl Display;
    }

    impl Producer for String {
        fn produce(&self) -> impl Display {
            self.clone()
        }
    }

    impl Producer for i32 {
        fn produce(&self) -> impl Display {
            *self
        }
    }

    /// 更复杂的用法：返回迭代器
    pub trait DataSource {
        fn items(&self) -> impl Iterator<Item = i32> + '_;
    }

    impl DataSource for Vec<i32> {
        fn items(&self) -> impl Iterator<Item = i32> + '_ {
            self.iter().copied()
        }
    }

    pub fn demonstrate() {
        println!("=== RPITIT (impl Trait in traits) ===\n");

        let s = String::from("hello");
        let i = 42;

        println!("String produces: {}", s.produce());
        println!("i32 produces: {}", i.produce());

        let data = vec![1, 2, 3, 4, 5];
        let sum: i32 = data.items().sum();
        println!("Sum from DataSource: {}", sum);

        println!();
    }
}

/// # 6. 异步 trait - Rust 1.75+
///
/// 原生异步 trait 支持
mod async_trait_native {
    use std::future::Future;

    /// 异步 trait（需要 async-trait crate 的时代）
    /// 现在可以直接在 trait 中使用 async fn
    pub trait DataFetcher {
        async fn fetch(&self, url: &str) -> Result<String, String>;

        async fn fetch_multiple(&self, urls: &[&str]) -> Vec<Result<String, String>> {
            let mut results = Vec::new();
            for url in urls {
                results.push(self.fetch(url).await);
            }
            results
        }
    }

    /// 实现异步 trait
    pub struct HttpFetcher;

    impl DataFetcher for HttpFetcher {
        async fn fetch(&self, url: &str) -> Result<String, String> {
            // 模拟异步请求
            Ok(format!("Fetched: {}", url))
        }
    }

    /// 返回 Future 的 trait 方法
    pub trait AsyncProcessor {
        fn process<'a>(&'a self, data: &'a str) -> impl Future<Output = String> + 'a;
    }

    pub fn demonstrate() {
        println!("=== 异步 trait ===\n");
        println!("Rust 1.75+ 支持原生 async fn in traits");
        println!("不再需要 async-trait crate");
        println!();
    }
}

/// # 7. 类型推导和模式匹配改进
mod type_inference_patterns {
    /// 更智能的类型推导
    pub fn smart_inference() {
        // 编译器现在可以更好地推导类型
        let numbers = vec![1, 2, 3, 4, 5]; // 无需显式类型标注
        let doubled: Vec<i32> = numbers.iter().map(|x| x * 2).collect();

        // 闭包参数类型推导
        let sum: i32 = doubled.iter().fold(0, |acc, x| acc + x);
        println!("Sum: {}", sum);
    }

    /// 解构赋值改进
    pub fn destructuring_patterns() {
        let pair = (1, "hello");
        let (a, b) = pair;
        println!("a={}, b={}", a, b);

        // 嵌套解构
        let nested = ((1, 2), (3, 4));
        let ((x1, y1), (x2, y2)) = nested;
        println!("Points: ({}, {}) and ({}, {})", x1, y1, x2, y2);

        // 结构体解构
        struct Point {
            x: i32,
            y: i32,
        }

        let p = Point { x: 10, y: 20 };
        let Point { x, y } = p;
        println!("Point: ({}, {})", x, y);
    }

    /// if let 链
    pub fn if_let_chains() {
        let first: Option<i32> = Some(1);
        let second: Option<i32> = Some(2);

        // 可以使用 && 连接多个 if let
        // 注意：需要 #![feature(let_chains)]，预计在稳定版中可用
        if let (Some(f), Some(s)) = (first, second) {
            println!("Both present: {} and {}", f, s);
        }
    }

    pub fn demonstrate() {
        println!("=== 类型推导和模式匹配 ===\n");

        smart_inference();
        destructuring_patterns();
        if_let_chains();

        println!();
    }
}

/// # 8. 新的标准库 API
mod new_std_apis {
    /// Option 的新方法
    pub fn option_new_methods() {
        let x: Option<i32> = Some(5);

        // is_some_and (Rust 1.70+)
        let is_positive = x.is_some_and(|v| v > 0);
        println!("Is positive: {}", is_positive);

        // inspect (Rust 1.76+)
        let y: Option<i32> = x.inspect(|v| println!("Inspecting: {}", v));
        println!("After inspect: {:?}", y);
    }

    /// slice 的新方法
    pub fn slice_new_methods() {
        let _arr = [1, 2, 3, 4, 5];

        // as_chunks (Rust 1.77+)
        // let (chunks, remainder) = arr.as_chunks::<2>();
        // println!("Chunks: {:?}, Remainder: {:?}", chunks, remainder);

        // split_once (类似字符串方法)
        // Rust 1.77+ 新增了许多实用的 slice 方法
    }

    /// HashMap 的新方法
    pub fn hashmap_new_methods() {
        let mut map = std::collections::HashMap::new();
        map.insert("a", 1);
        map.insert("b", 2);

        // get_many_mut (Rust 1.86+ 实验性)
        // 允许同时获取多个可变引用
    }

    pub fn demonstrate() {
        println!("=== 新的标准库 API ===\n");

        option_new_methods();
        slice_new_methods();
        hashmap_new_methods();

        println!();
    }
}

fn main() {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║     现代 Rust 模式 (2024-2025)                            ║");
    println!("╚══════════════════════════════════════════════════════════╝");

    let_else_patterns::demonstrate();
    control_flow_patterns::demonstrate();
    inline_const::demonstrate();
    gat_patterns::demonstrate();
    rpitit_patterns::demonstrate();
    async_trait_native::demonstrate();
    type_inference_patterns::demonstrate();
    new_std_apis::demonstrate();

    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║     现代 Rust 特性总结                                    ║");
    println!("╠══════════════════════════════════════════════════════════╣");
    println!("║ • let...else          - 提前返回的优雅语法                ║");
    println!("║ • ControlFlow         - 自定义控制流抽象                  ║");
    println!("║ • inline const        - 编译期常量计算                    ║");
    println!("║ • GATs                - 泛型关联类型                      ║");
    println!("║ • RPITIT              - trait 中的 impl Trait             ║");
    println!("║ • async fn in traits  - 原生异步 trait                    ║");
    println!("║ • 类型推导改进         - 更智能的推断                      ║");
    println!("╚══════════════════════════════════════════════════════════╝");
}
