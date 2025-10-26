//! # Rust 1.89 特性示例 (历史版本)
//!
//! ⚠️ **注意**: 本示例针对 Rust 1.89 版本编写，部分特性在 Rust 1.90 中已有更新。
//!
//! ## Rust 1.90 主要更新
//!
//! ### 编译器改进
//! - **LLD 链接器**: Linux x86_64 默认启用，链接速度提升约 2x
//! - **编译性能**: 增量编译优化，构建速度提升
//!
//! ### 标准库更新
//! - `u{n}::checked_sub_signed()` - 新增带符号减法检查方法
//! - `<[T]>::reverse()` - 现在可在 const 上下文中使用
//! - `f32/f64` 数学函数 - floor/ceil/trunc 等在 const 中可用
//!
//! ### Lint 改进
//! - `mismatched_lifetime_syntaxes` - 默认启用，检查生命周期语法一致性
//!
//! ## 迁移建议
//!
//! 1. 更新 Cargo.toml: `rust-version = "1.90"`, `edition = "2024"`
//! 2. 应用新的稳定 API 和 const 函数增强
//! 3. 检查并修复新 lint 警告
//!
//! 参考: [Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
//!
//! ---
//!
//! # Rust 1.89 增强特性演示
//!
//! 本示例展示 Rust 1.89 版本的最新特性：
//! - let_chains 特性稳定化
//! - cfg_boolean_literals 特性稳定化
//! - 裸函数支持稳定化
//! - 危险隐式引用警告
//! - 无效空指针参数校验

use c03_control_fn::rust_189_enhanced_features::*;

#[tokio::main]
async fn main() {
    println!("🚀 Rust 1.89 增强特性演示程序");
    println!("=====================================");
    println!();

    // 运行所有增强特性演示
    Rust189EnhancedFeatures::run_all_demonstrations();

    println!();
    println!("📋 Rust 1.89 特性列表:");
    println!("========================");

    let features = Rust189EnhancedFeatures::get_feature_list();
    for (i, feature) in features.iter().enumerate() {
        println!("{}. {}", i + 1, feature);
    }

    println!();
    println!("🔍 特性支持状态检查:");
    println!("====================");

    let support_status = Rust189EnhancedFeatures::check_feature_support();
    for (feature, supported) in support_status {
        let status = if supported {
            "✅ 支持"
        } else {
            "❌ 不支持"
        };
        println!("{}: {}", feature, status);
    }

    println!();
    println!("🎯 实际应用场景演示:");
    println!("====================");

    // 实际应用场景演示
    demonstrate_real_world_usage();

    println!();
    println!("✅ 演示完成！");
}

/// 实际应用场景演示
fn demonstrate_real_world_usage() {
    println!("=== 实际应用场景演示 ===");

    // 场景1：用户权限检查
    demonstrate_user_permission_check();

    // 场景2：配置管理
    demonstrate_configuration_management();

    // 场景3：错误处理
    demonstrate_error_handling();
}

/// 用户权限检查场景
fn demonstrate_user_permission_check() {
    println!("--- 用户权限检查场景 ---");

    #[derive(Debug)]
    struct User {
        id: u32,
        role: Option<String>,
        permissions: Vec<String>,
    }

    let user = User {
        id: 12345,
        role: Some("admin".to_string()),
        permissions: vec![
            "read".to_string(),
            "write".to_string(),
            "delete".to_string(),
        ],
    };

    // 使用 let_chains 进行复杂的权限检查
    if let Some(role) = &user.role
        && role == "admin"
        && user.permissions.contains(&"delete".to_string())
        && user.id > 1000
    {
        println!("✅ 用户 {} 具有管理员删除权限", user.id);
    } else {
        println!("❌ 用户权限不足");
    }
}

/// 配置管理场景
fn demonstrate_configuration_management() {
    println!("--- 配置管理场景 ---");

    #[derive(Debug)]
    struct Config {
        database_url: Option<String>,
        api_key: Option<String>,
        debug_mode: bool,
    }

    let config = Config {
        database_url: Some("postgresql://localhost:5432/mydb".to_string()),
        api_key: Some("secret_key_123".to_string()),
        debug_mode: true,
    };

    // 使用 let_chains 进行配置验证
    if let Some(db_url) = &config.database_url
        && db_url.starts_with("postgresql://")
        && let Some(api_key) = &config.api_key
        && api_key.len() > 10
        && config.debug_mode
    {
        println!("✅ 配置验证通过，可以启动应用");
        println!("   数据库: {}", db_url);
        println!("   API密钥长度: {}", api_key.len());
        println!("   调试模式: {}", config.debug_mode);
    } else {
        println!("❌ 配置验证失败");
    }
}

/// 错误处理场景
fn demonstrate_error_handling() {
    println!("--- 错误处理场景 ---");

    // 模拟文件操作
    let file_path = "/path/to/file.txt";
    let file_content = Some("Hello, World!".to_string());

    // 使用 let_chains 进行错误处理
    if let Some(content) = file_content
        && !content.is_empty()
        && content.len() > 5
        && file_path.ends_with(".txt")
    {
        println!("✅ 文件读取成功: {}", file_path);
        println!("   内容长度: {}", content.len());
        println!("   内容预览: {}", &content[..10.min(content.len())]);
    } else {
        println!("❌ 文件读取失败或内容无效");
    }
}

/// 条件编译演示
#[cfg(target_os = "linux")]
fn _demonstrate_platform_specific_features() {
    println!("--- Linux 平台特定功能 ---");
    println!("✅ 运行在 Linux 平台上");
}

#[cfg(target_os = "windows")]
fn _demonstrate_platform_specific_features() {
    println!("--- Windows 平台特定功能 ---");
    println!("✅ 运行在 Windows 平台上");
}

#[cfg(not(any(target_os = "linux", target_os = "windows")))]
fn _demonstrate_platform_specific_features() {
    println!("--- 其他平台功能 ---");
    println!("✅ 运行在其他平台上");
}

/// 性能优化演示
fn _demonstrate_performance_optimizations() {
    println!("--- 性能优化演示 ---");

    // 使用常量泛型进行编译时优化
    const MATRIX_SIZE: usize = 1000;
    let _matrix: [[f64; MATRIX_SIZE]; MATRIX_SIZE] = [[0.0; MATRIX_SIZE]; MATRIX_SIZE];

    println!("✅ 创建了 {}x{} 的矩阵", MATRIX_SIZE, MATRIX_SIZE);

    // 编译时计算
    const FACTORIAL_10: u64 = {
        let mut result = 1;
        let mut i = 1;
        while i <= 10 {
            result *= i;
            i += 1;
        }
        result
    };

    println!("✅ 编译时计算的 10! = {}", FACTORIAL_10);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_user_permission_check() {
        demonstrate_user_permission_check();
    }

    #[test]
    fn test_configuration_management() {
        demonstrate_configuration_management();
    }

    #[test]
    fn test_error_handling() {
        demonstrate_error_handling();
    }

    #[test]
    fn test_platform_specific_features() {
        demonstrate_platform_specific_features();
    }

    #[test]
    fn test_performance_optimizations() {
        demonstrate_performance_optimizations();
    }
}
