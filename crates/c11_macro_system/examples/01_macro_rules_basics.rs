//! # 示例01: macro_rules!基础
//! 本示例演示声明宏的基本用法
//! this example demonstration this
//! ## 📐 知识结构
//! ## 📐 structure
//! ## 📐 知识structure
//! ### 核心概念
//! ### core concept
//!   - **属性**: 模式匹配、宏展开、代码生成
//!   - **attribute **: 、、
//!   - **attribute**: 模式匹配、宏展开、代码Generate
//!   - **attribute**: 、、Generate
//!   - **关系**: 与宏系统、代码生成相关
//!   - ****: and system 、
//! ### 思维导图
//! ###
//! macro_rules! 基础
//! ├── 简单宏
//! ├── simple
//! │   └── 无参数宏
//! │ └── parameter
//! ├── 函数创建
//! ├── function
//! │   └── 代码生成
//! │ └──
//! │ └── 代码Generate
//! ├── 表达式计算
//! ├── express
//! │   └── 编译时计算
//! │ └── compile-time
//! └── 向量创建
//! └──
//! └── 向量Create
//!     └── 便捷语法
//!     └──
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
    println!(
        "count!(1, 2, 3, 4, 5) = {}",
        c11_macro_system::count!(1, 2, 3, 4, 5)
    );
    println!();

    // 6. 递归宏 - 最大值
    println!("6. 递归宏 - 最大值:");
    println!("max!(10, 5, 20, 15) = {}", max!(10, 5, 20, 15));
    println!();

    println!("=== 示例完成 ===");
}
