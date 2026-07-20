//! 特质约束案例
//! 
//! 本模块演示特质约束的各种用法，包括单一约束、多重约束、where子句等。
//! 
//! 理论映射：
//! - 特质约束: T: Display → B = (α, T)
//! - 多重约束: T: Display + Debug → B = (α, T₁ + T₂)
//! - where子句: where T: Display → 复杂约束表达式

use std::fmt::{Display, Debug};

/// 基础特质约束
/// 
/// 理论映射：B = (α, T)
/// - α: T (类型参数)
/// - T: Display (特质约束)
pub fn print_item<T: Display>(item: T) {
    println!("Item: {}", item);
}

/// 多重特质约束
/// 
/// 理论映射：B = (α, T₁ + T₂)
/// - α: T (类型参数)
/// - T₁: Display
/// - T₂: Debug
pub fn print_and_debug<T: Display + Debug>(item: T) {
    println!("Display: {}", item);
    println!("Debug: {:?}", item);
}

/// where子句约束
/// 
/// 理论映射：where子句提供复杂约束表达式
pub fn complex_function<T, U>(item: T, other: U) 
where 
    T: Display + Debug,
    U: Display + Clone,
{
    println!("Item: {}", item);
    println!("Debug: {:?}", item);
    println!("Other: {}", other);
    
    let cloned = other.clone();
    println!("Cloned: {}", cloned);
}

/// 关联类型约束
/// 
/// 理论映射：关联类型在约束中的使用
pub trait Container {
    type Item;
    fn get(&self) -> Option<&Self::Item>;
    fn set(&mut self, item: Self::Item);
}

/// 泛型容器
pub struct GenericContainer<T> {
    item: Option<T>,
}

impl<T> Container for GenericContainer<T> {
    type Item = T;
    
    fn get(&self) -> Option<&Self::Item> {
        self.item.as_ref()
    }
    
    fn set(&mut self, item: Self::Item) {
        self.item = Some(item);
    }
}

/// 使用关联类型约束的函数
/// 
/// 理论映射：关联类型约束 C::Item: Display
pub fn print_container<C>(container: &C) 
where 
    C: Container,
    C::Item: Display,
{
    if let Some(item) = container.get() {
        println!("Container item: {}", item);
    } else {
        println!("Container is empty");
    }
}

/// 生命周期约束
/// 
/// 理论映射：生命周期在特质约束中的使用
pub trait HasLifetime<'a> {
    fn get_ref(&self) -> &'a str;
}

pub struct StringWrapper {
    data: String,
}

impl<'a> HasLifetime<'a> for StringWrapper {
    fn get_ref(&self) -> &'a str {
        &self.data
    }
}

/// 使用生命周期约束的函数
pub fn process_with_lifetime<T>(item: &T) 
where 
    for<'a> T: HasLifetime<'a>,
{
    let ref_data = item.get_ref();
    println!("Lifetime data: {}", ref_data);
}

/// 特质约束的组合
/// 
/// 理论映射：复杂约束组合
pub trait Numeric: Display + Debug + PartialOrd + Clone {}

impl<T> Numeric for T 
where 
    T: Display + Debug + PartialOrd + Clone,
{}

/// 使用组合约束的函数
pub fn process_numeric<T: Numeric>(items: &[T]) {
    for (i, item) in items.iter().enumerate() {
        println!("Item {}: {} (debug: {:?})", i, item, item);
    }
    
    if items.len() > 1 {
        let first = &items[0];
        let second = &items[1];
        
        match first.partial_cmp(second) {
            Some(std::cmp::Ordering::Less) => println!("First < Second"),
            Some(std::cmp::Ordering::Equal) => println!("First == Second"),
            Some(std::cmp::Ordering::Greater) => println!("First > Second"),
            None => println!("Cannot compare"),
        }
    }
}

/// 条件特质约束
/// 
/// 理论映射：条件约束 where T: SomeTrait
pub trait Conditional {
    fn process(&self);
}

impl<T> Conditional for T 
where 
    T: Display,
{
    fn process(&self) {
        println!("Processing: {}", self);
    }
}

/// 使用条件约束的函数
pub fn use_conditional<T>(item: T) 
where 
    T: Conditional,
{
    item.process();
}

/// 特质约束的递归使用
/// 
/// 理论映射：递归约束 T: Container where T::Item: Display
pub fn print_container_recursive<C>(container: &C) 
where 
    C: Container,
    C::Item: Display,
{
    if let Some(item) = container.get() {
        println!("Container item: {}", item);
    }
}

/// 特质约束的默认实现
/// 
/// 理论映射：基于约束的默认实现
pub trait Processable {
    fn process(&self);
    
    /// 默认实现，基于特质约束
    fn process_with_info(&self) 
    where 
        Self: Display,
    {
        println!("Processing with info: {}", self);
        self.process();
    }
}

impl<T> Processable for T 
where 
    T: Display,
{
    fn process(&self) {
        println!("Processing: {}", self);
    }
}

/// 特质约束的性能优化
/// 
/// 理论映射：零成本抽象保证
pub trait Optimized {
    fn fast_operation(&self);
    
    /// 默认实现，编译期优化
    fn optimized_operation(&self) 
    where 
        Self: Copy + Display,
    {
        println!("Optimized operation for: {}", self);
        self.fast_operation();
    }
}

impl<T> Optimized for T 
where 
    T: Copy + Display,
{
    fn fast_operation(&self) {
        // 编译期优化的操作
        println!("Fast operation: {}", self);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 测试基础特质约束
    #[test]
    fn test_basic_trait_bounds() {
        let number = 42;
        let text = "Hello, World!";
        
        print_item(number);
        print_item(text);
    }

    /// 测试多重约束
    #[test]
    fn test_multiple_bounds() {
        let number = 42;
        let text = "Hello";
        
        print_and_debug(number);
        print_and_debug(text);
    }

    /// 测试where子句
    #[test]
    fn test_where_clause() {
        let number = 42;
        let text = "Hello".to_string();
        
        complex_function(number, text);
    }

    /// 测试关联类型约束
    #[test]
    fn test_associated_type_bounds() {
        let mut container = GenericContainer { item: None };
        container.set(42);
        
        print_container(&container);
    }

    /// 测试生命周期约束
    #[test]
    fn test_lifetime_bounds() {
        let wrapper = StringWrapper {
            data: "Hello, Lifetime!".to_string(),
        };
        
        process_with_lifetime(&wrapper);
    }

    /// 测试组合约束
    #[test]
    fn test_combined_bounds() {
        let numbers = vec![1, 2, 3, 4, 5];
        process_numeric(&numbers);
    }

    /// 测试条件约束
    #[test]
    fn test_conditional_bounds() {
        let number = 42;
        let text = "Hello";
        
        use_conditional(number);
        use_conditional(text);
    }

    /// 测试递归约束
    #[test]
    fn test_recursive_bounds() {
        let mut container = GenericContainer { item: None };
        container.set("Recursive bound test");
        
        print_container_recursive(&container);
    }

    /// 测试默认实现约束
    #[test]
    fn test_default_impl_bounds() {
        let number = 42;
        let text = "Hello";
        
        number.process_with_info();
        text.process_with_info();
    }

    /// 测试优化约束
    #[test]
    fn test_optimization_bounds() {
        let number = 42;
        let text = "Hello";
        
        number.optimized_operation();
        text.optimized_operation();
    }
}

/// 示例用法
pub fn run_examples() {
    println!("=== 特质约束案例 ===");
    
    // 基础约束
    println!("1. 基础约束:");
    print_item(42);
    print_item("Hello, World!");
    
    // 多重约束
    println!("\n2. 多重约束:");
    print_and_debug(42);
    print_and_debug("Hello");
    
    // where子句
    println!("\n3. where子句:");
    complex_function(42, "Hello".to_string());
    
    // 关联类型约束
    println!("\n4. 关联类型约束:");
    let mut container = GenericContainer { item: None };
    container.set("Associated type test");
    print_container(&container);
    
    // 生命周期约束
    println!("\n5. 生命周期约束:");
    let wrapper = StringWrapper {
        data: "Lifetime test".to_string(),
    };
    process_with_lifetime(&wrapper);
    
    // 组合约束
    println!("\n6. 组合约束:");
    let numbers = vec![1, 2, 3, 4, 5];
    process_numeric(&numbers);
    
    // 条件约束
    println!("\n7. 条件约束:");
    use_conditional(42);
    use_conditional("Hello");
    
    // 默认实现约束
    println!("\n8. 默认实现约束:");
    let number = 42;
    number.process_with_info();
    
    // 优化约束
    println!("\n9. 优化约束:");
    number.optimized_operation();
} 