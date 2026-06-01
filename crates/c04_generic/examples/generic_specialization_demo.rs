//! 泛型特化模拟示例
//! generic example
//! - 实际应用场景
//! - actual application scenario
//! 本示例展示如何使用现有特性模拟特化效果
//! this example feature effect
//! 运行方式:
//! Run way :
//! cargo run --example generic_specialization_demo
//! ```
use std::fmt::Display;

/// 序列化trait
/// sequence trait
trait Serialize {
    fn serialize(&self) -> String;
}

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

impl Serialize for String {
    fn serialize(&self) -> String {
        format!("String(\"{}\")", self)
    }
}

trait OptimizedSerialize {
    fn optimized_serialize(&self) -> String;
}

/// 通用实现
/// 通用Implementation of
impl<T: Display> OptimizedSerialize for T {
    fn optimized_serialize(&self) -> String {
        format!("Generic: {}", self)
    }
}

trait IntSerialize: OptimizedSerialize {
    fn int_serialize(&self) -> String;
}

impl IntSerialize for i32 {
    fn int_serialize(&self) -> String {
        format!("Integer({})", self)
    }
}

/// 使用类型标记实现特化
/// type mark
#[allow(dead_code)]
trait Converter<T> {
    fn convert(&self) -> T;
}

/// i32到f64的转换器
/// i32to f64conversion
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
    println!(
        "数字 {} 的通用序列化: {}",
        number,
        number.optimized_serialize()
    );
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
