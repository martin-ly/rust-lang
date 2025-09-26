/*
Rust 的泛型机制是其强大类型系统的重要组成部分，允许开发者编写灵活、可重用的代码。
以下是 Rust 泛型机制的核心定义、概念、解释和示例。

泛型类型generic type：
    泛型类型是指在定义结构体、枚举或特征时使用的占位符类型。
    它允许您在不指定具体类型的情况下编写代码。

泛型函数generic function：
    泛型函数是可以接受不同类型参数的函数。
    通过使用泛型，您可以编写更通用的逻辑。

泛型特征generic trait：
    特征是 Rust 中的一个重要概念，定义了一组方法的接口。
    您可以为泛型类型实现特征，从而使其具备特定的行为。

泛型约束generic Bounds：
    约束用于限制泛型类型的具体类型。
    例如，您可以指定一个泛型类型必须实现某个特征。

泛型实现generic implementation：
    泛型实现是 Rust 中的一个重要概念，定义了泛型类型必须满足的条件。

生命周期（Lifetimes）：
    生命周期是 Rust 的另一个重要概念，确保引用在使用时是有效的。
    泛型和生命周期可以结合使用，以确保安全性。
*/
use std::collections::HashMap;

#[allow(unused)]
// 定义一个泛型结构体
pub struct Point<T> {
    pub x: T,
    pub y: T,
}

// 定义一个特征
pub trait Summarizable {
    fn summarize(&self) -> String;
}

// 为 String 实现 Summarizable 特征
impl Summarizable for String {
    fn summarize(&self) -> String {
        format!("Summary: {}", self)
    }
}

// 泛型函数，接受实现了 Summarizable 特征的类型
pub fn summarize_item<T: Summarizable>(item: T) {
    println!("{}", item.summarize());
}

#[allow(unused)]
// 定义一个泛型函数，要求 T 实现 PartialOrd 特征
#[allow(clippy::type_complexity)]
pub fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];

    for item in list {
        if item > largest {
            largest = item;
        }
    }

    largest // 返回最大的元素
}

#[allow(unused)]
// 定义一个带有生命周期参数的函数
pub fn longest<'a>(s1: &'a str, s2: &'a str) -> &'a str {
    if s1.len() > s2.len() { s1 } else { s2 }
}

// 定义一个特征
pub trait Describable {
    fn describe(&self) -> String;
}

// 为结构体实现特征
#[allow(unused)]
pub struct Dog {
    pub name: String,
}

impl Describable for Dog {
    fn describe(&self) -> String {
        format!("This is a dog named {}", self.name)
    }
}

// 泛型函数，接受实现了 Describable 特征的类型
pub fn print_description<T: Describable>(item: T) {
    println!("{}", item.describe());
}

//泛型集合类型
#[allow(unused)]
#[allow(clippy::type_complexity)]
pub fn hashmap_test() {
    let mut scores: HashMap<String, i32> = HashMap::new();
    scores.insert(String::from("Alice"), 50);
    scores.insert(String::from("Bob"), 70);

    for (name, score) in &scores {
        println!("{}: {}", name, score);
    }
}
