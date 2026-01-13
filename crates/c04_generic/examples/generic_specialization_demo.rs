//! 泛型特化模拟示例
//!
//! 本示例展示如何在Rust中模拟泛型特化（使用trait和newtype模式）：
//! - 使用trait实现特化
//! - 使用newtype模式实现特化
//! - 实际应用场景
//!
//! 注意：Rust稳定版目前不支持真正的泛型特化（specialization）
//! 本示例展示如何使用现有特性模拟特化效果
//!
//! 运行方式:
//! ```bash
//! cargo run --example generic_specialization_demo
//! ```

use std::fmt::Display;

/// 序列化trait
trait Serialize {
    fn serialize(&self) -> String;
}

/// 使用newtype模式为i32提供特化实现
struct IntValue(i32);

impl Display for IntValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Serialize for IntValue {
    fn serialize(&self) -> String {
        format!("Integer({})", self.0)
    }
}

/// 通用实现 - 为所有实现Display的类型提供默认实现
/// 注意：这里只为部分类型实现，避免与IntValue冲突
impl Serialize for String {
    fn serialize(&self) -> String {
        format!("String(\"{}\")", self)
    }
}

/// 使用trait实现特化模式
trait OptimizedSerialize {
    fn optimized_serialize(&self) -> String;
}

/// 通用实现
impl<T: Display> OptimizedSerialize for T {
    fn optimized_serialize(&self) -> String {
        format!("Generic: {}", self)
    }
}

/// 为i32提供优化实现（通过扩展trait）
trait IntSerialize: OptimizedSerialize {
    fn int_serialize(&self) -> String;
}

impl IntSerialize for i32 {
    fn int_serialize(&self) -> String {
        format!("Integer({})", self)
    }
}

/// 使用类型标记实现特化
#[allow(dead_code)]
trait Converter<T> {
    fn convert(&self) -> T;
}

/// i32到f64的转换器
#[allow(dead_code)]
struct IntToFloat;

#[allow(dead_code)]
impl Converter<f64> for IntToFloat {
    fn convert(&self) -> f64 {
        0.0
    }
}

fn convert_i32_to_f64(value: i32) -> f64 {
    value as f64
}

fn main() {
    println!("🚀 泛型特化模拟示例\n");
    println!("{}", "=".repeat(60));

    // 1. 使用newtype模式实现特化
    println!("\n📊 Newtype模式特化:");
    println!("{}", "-".repeat(60));
    let int_value = IntValue(42);
    println!("整数特化序列化: {}", int_value.serialize());

    let normal_int: i32 = 42;
    println!("整数原始值: {}", normal_int);

    // 2. 使用trait扩展实现特化
    println!("\n📊 Trait扩展特化:");
    println!("{}", "-".repeat(60));
    let number: i32 = 42;
    println!("数字 {} 的通用序列化: {}", number, number.optimized_serialize());
    println!("数字 {} 的特化序列化: {}", number, number.int_serialize());

    let text = "Hello";
    println!("文本 \"{}\" 的序列化: {}", text, text.optimized_serialize());

    // 3. 使用转换函数实现特化
    println!("\n📊 转换函数特化:");
    println!("{}", "-".repeat(60));
    let int_val: i32 = 42;
    let float_val = convert_i32_to_f64(int_val);
    println!("整数 {} 转换为浮点数: {}", int_val, float_val);

    println!("\n💡 泛型特化说明:");
    println!("{}", "-".repeat(60));
    println!("  ⚠️  Rust稳定版目前不支持真正的泛型特化（specialization）");
    println!("  ✅ 可以使用newtype模式实现特化");
    println!("  ✅ 可以使用trait扩展实现特化");
    println!("  ✅ 可以使用转换函数实现特化");
    println!("  ✅ 可以使用trait对象实现运行时特化");

    println!("\n✅ 演示完成！");
}
