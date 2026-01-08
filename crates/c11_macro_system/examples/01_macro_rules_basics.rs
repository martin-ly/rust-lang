//! # 示例01: macro_rules!基础
//!
//! 本示例演示声明宏的基本用法
//!
//! ## 📐 知识结构
//!
//! ### 核心概念
//!
//! - **声明宏 (Declarative Macros)**: 使用 macro_rules! 定义的宏
//!   - **属性**: 模式匹配、宏展开、代码生成
//!   - **关系**: 与宏系统、代码生成相关
//!
//! ### 思维导图
//!
//! ```text
//! macro_rules! 基础
//! │
//! ├── 简单宏
//! │   └── 无参数宏
//! ├── 函数创建
//! │   └── 代码生成
//! ├── 表达式计算
//! │   └── 编译时计算
//! └── 向量创建
//!     └── 便捷语法
//! ```

use c11_macro_system::*;

fn main() {
    println!("=== macro_rules! 基础示例 ===\n");

    // 1. 简单宏调用
    println!("1. 简单宏:");
    say_hello!();
    println!();

    // 2. 创建函数
    println!("2. 创建函数:");
    create_function!(greet);
    greet();
    println!();

    // 3. 计算表达式
    println!("3. 计算表达式:");
    let result = calculate!(5 + 3 * 2);
    println!("计算结果: {}\n", result);

    // 4. 创建字符串向量
    println!("4. 创建字符串向量:");
    let strings = vec_of_strings!["Rust", "Macros", "Are", "Powerful"];
    println!("字符串向量: {:?}\n", strings);

    // 5. 递归宏 - 计数
    println!("5. 递归宏 - 计数:");
    println!("count!(1, 2, 3, 4, 5) = {}", count!(1, 2, 3, 4, 5));
    println!();

    // 6. 递归宏 - 最大值
    println!("6. 递归宏 - 最大值:");
    println!("max!(10, 5, 20, 15) = {}", max!(10, 5, 20, 15));
    println!();

    println!("=== 示例完成 ===");
}
