//! 高阶Trait边界（HRTB）示例
//!
//! 本示例展示HRTB（Higher-Rank Trait Bounds）的使用：
//! - HRTB的基本语法
//! - for<'a> 语法
//! - 实际应用场景
//!
//! 运行方式:
//! ```bash
//! cargo run --example generic_hrtb_demo
//! ```

/// 带有生命周期参数的trait
trait Processor<'a> {
    type Input;
    type Output;

    fn process(&self, input: Self::Input) -> Self::Output;
}

/// 字符串处理器
struct StringProcessor;

impl<'a> Processor<'a> for StringProcessor {
    type Input = &'a str;
    type Output = String;

    fn process(&self, input: &'a str) -> String {
        input.to_uppercase()
    }
}

/// 使用HRTB的函数
fn process_with_hrtb<P>(processor: P, input: &str) -> String
where
    P: for<'a> Processor<'a, Input = &'a str, Output = String>,
{
    processor.process(input)
}

/// 借用迭代器trait
trait LendingIterator {
    type Item<'a>
    where
        Self: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

/// 数字迭代器
struct NumberIterator {
    numbers: Vec<i32>,
    index: usize,
}

impl NumberIterator {
    fn new(numbers: Vec<i32>) -> Self {
        Self { numbers, index: 0 }
    }
}

impl LendingIterator for NumberIterator {
    type Item<'a> = &'a i32
    where
        Self: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>> {
        if self.index < self.numbers.len() {
            let item = &self.numbers[self.index];
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }
}

/// 使用HRTB处理迭代器
fn process_iterator<I>(mut iterator: I) -> Vec<i32>
where
    I: for<'a> LendingIterator<Item<'a> = &'a i32>,
{
    let mut result = Vec::new();
    while let Some(item) = iterator.next() {
        result.push(*item * 2);
    }
    result
}

fn main() {
    println!("🚀 高阶Trait边界（HRTB）示例\n");
    println!("{}", "=".repeat(60));

    // 1. 使用HRTB处理字符串
    println!("\n📊 HRTB字符串处理示例:");
    println!("{}", "-".repeat(60));
    let processor = StringProcessor;
    let input = "hello, world!";
    let output = process_with_hrtb(processor, input);
    println!("输入: {}", input);
    println!("输出: {}", output);

    // 2. 使用HRTB处理迭代器
    println!("\n📊 HRTB迭代器处理示例:");
    println!("{}", "-".repeat(60));
    let numbers = vec![1, 2, 3, 4, 5];
    let iterator = NumberIterator::new(numbers.clone());
    let doubled = process_iterator(iterator);
    println!("原始数字: {:?}", numbers);
    println!("加倍后: {:?}", doubled);

    // 3. HRTB说明
    println!("\n💡 HRTB说明:");
    println!("{}", "-".repeat(60));
    println!("  ✅ for<'a> 语法表示对所有生命周期 'a 都成立");
    println!("  ✅ 用于处理带有生命周期参数的trait");
    println!("  ✅ 提供更灵活的类型约束");
    println!("  ✅ 常用于借用迭代器和异步代码");

    println!("\n✅ 演示完成！");
}
