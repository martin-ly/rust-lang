//! # Rust 1.89 特性示例 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features.rs`
//!
//! ## 版本历史说明
//!
//! 本文件展示 Rust 1.89 版本的特性，当前项目已升级到 Rust 1.92.0。
//!
//! ### Rust 1.92.0 主要改进
//!
//! - **语言特性**: MaybeUninit 文档化、联合体原始引用、关联项多边界等
//! - **标准库**: NonZero::div_ceil、rotate_right、Location::file_as_c_str
//! - **性能优化**: 迭代器方法特化、改进的编译优化
//!
//! ### 迁移建议
//!
//! 1. 更新 Cargo.toml: `rust-version = "1.92"`
//! 2. 参考 `rust_192_features.rs` 了解最新特性
//! 3. 查看 `docs/RUST_192_CONTROL_FLOW_IMPROVEMENTS.md` 了解完整改进
//!
//! 参考:
//! - [Rust 1.92.0 Release Notes](https://releases.rs/docs/1.92.0/)
//! - [历史版本: Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
//!
//! ---
//!
//! # Rust 1.89 增强特性模块
//!
//! 本模块包含 Rust 1.89 版本的最新特性实现，包括：
//! - let_chains 特性稳定化
//! - cfg_boolean_literals 特性稳定化
//! - 裸函数支持稳定化
//! - 危险隐式引用警告
//! - 无效空指针参数校验
// 移除未使用的导入

/// Rust 1.89 let_chains 特性演示
pub mod let_chains_189 {

    /// 用户状态枚举
    #[derive(Debug, Clone)]
    pub enum UserStatus {
        Active(u32, String),
        Inactive,
        Pending,
    }

    /// 获取当前用户状态
    pub fn get_current_user_status() -> UserStatus {
        UserStatus::Active(12345, "Rustacean".to_string())
    }

    /// let_chains 特性演示
    pub fn demonstrate_let_chains() {
        println!("=== Rust 1.89 let_chains 特性演示 ===");

        // 使用 let_chains 进行复杂条件判断
        if let UserStatus::Active(id, name) = get_current_user_status()
            && (10000..99999).contains(&id)
            && name.len() > 5
        {
            println!("✅ 找到符合条件的用户：ID {}, 名字 '{}'", id, name);
        } else {
            println!("❌ 未找到符合条件的用户");
        }

        // 更复杂的 let_chains 示例
        let data = [Some(42), Some(100), None, Some(200)];

        for (i, item) in data.iter().enumerate() {
            if let Some(value) = item
                && *value > 50
                && *value < 150
                && i % 2 == 0
            {
                println!("✅ 索引 {} 的值 {} 满足条件", i, value);
            }
        }
    }

    /// 嵌套结构体的 let_chains 演示
    #[derive(Debug)]
    pub struct User {
        pub id: u32,
        pub profile: Option<UserProfile>,
    }

    #[derive(Debug)]
    pub struct UserProfile {
        pub name: String,
        pub email: Option<String>,
    }

    pub fn demonstrate_nested_let_chains() {
        println!("=== 嵌套结构体 let_chains 演示 ===");

        let user = User {
            id: 12345,
            profile: Some(UserProfile {
                name: "Alice".to_string(),
                email: Some("alice@example.com".to_string()),
            }),
        };

        // 使用 let_chains 处理嵌套结构
        if let Some(profile) = &user.profile
            && profile.name.len() > 3
            && let Some(email) = &profile.email
            && email.contains("@")
            && user.id > 1000
        {
            println!(
                "✅ 用户 {} (ID: {}) 有有效的邮箱: {}",
                profile.name, user.id, email
            );
        } else {
            println!("❌ 用户信息不完整或无效");
        }
    }
}

/// Rust 1.89 cfg_boolean_literals 特性演示
pub mod cfg_boolean_literals_189 {

    /// 始终启用的功能
    #[cfg(true)]
    pub fn feature_always_on() {
        println!("✅ 这是一个始终启用的功能");
    }

    /// 永远不会启用的功能
    #[cfg(false)]
    pub fn feature_never_on() {
        // 此函数不会被编译
        println!("这个函数永远不会被编译");
    }

    /// Linux 专属功能（结合布尔字面量）
    #[cfg(all(target_os = "linux", true))]
    pub fn linux_specific_feature() {
        println!("✅ 这是一个 Linux 专属功能");
    }

    /// Windows 专属功能
    #[cfg(all(target_os = "windows", true))]
    pub fn windows_specific_feature() {
        println!("✅ 这是一个 Windows 专属功能");
    }

    /// 条件编译演示
    pub fn demonstrate_cfg_boolean_literals() {
        println!("=== Rust 1.89 cfg_boolean_literals 特性演示 ===");

        feature_always_on();

        // 根据平台调用不同的功能
        #[cfg(target_os = "linux")]
        linux_specific_feature();

        #[cfg(target_os = "windows")]
        windows_specific_feature();

        // feature_never_on(); // 此函数未被编译，无法调用
    }

    /// 复杂的条件编译示例
    #[cfg(all(
        any(target_os = "linux", target_os = "macos"),
        true,
        not(debug_assertions)
    ))]
    pub fn production_unix_feature() {
        println!("✅ 生产环境的 Unix 系统功能");
    }
}

/// Rust 1.89 裸函数支持演示
pub mod naked_functions_189 {

    /// 裸函数示例（需要 unsafe 和 asm! 宏）
    /// 注意：这需要 nightly 版本和 asm! 宏支持
    #[cfg(all(feature = "nightly", target_arch = "x86_64"))]
    pub mod naked_functions {
        // 使用 nightly 的 naked_asm! 宏

        /// 简单的裸函数
        #[cfg(false)]
        #[naked]
        pub unsafe extern "C" fn simple_naked_function() -> ! {
            core::arch::naked_asm!(
                "nop\nret"
            );
        }

        /// 带参数的裸函数
        // 该示例需要更复杂的 ABI/保存约定，演示目的先禁用
        #[cfg(false)]
        #[naked]
        pub unsafe extern "C" fn naked_function_with_params(_x: i32) -> i32 {
            core::arch::naked_asm!(
                "ret"
            );
        }
    }

    /// 裸函数演示（安全版本）
    pub fn demonstrate_naked_functions() {
        println!("=== Rust 1.89 裸函数支持演示 ===");

        #[cfg(all(feature = "nightly", target_arch = "x86_64"))]
        {
            println!("✅ 裸函数支持已启用（需要 nightly 版本）");
            // 注意：实际调用裸函数需要特殊的环境和配置
        }

        #[cfg(not(all(feature = "nightly", target_arch = "x86_64")))]
        {
            println!("ℹ️ 裸函数支持需要 nightly 版本和 asm! 宏");
        }
    }
}

/// Rust 1.89 危险隐式引用警告演示
pub mod dangerous_implicit_autorefs_189 {

    /// 演示危险隐式引用
    pub fn demonstrate_dangerous_implicit_autorefs() {
        println!("=== Rust 1.89 危险隐式引用警告演示 ===");

        let mut x = 42;
        let ptr = &mut x as *mut i32;

        // 这种用法可能会触发危险隐式引用警告
        // 编译器会提醒显式管理指针借用
        unsafe {
            let value = *ptr;
            println!("✅ 通过指针获取值: {}", value);
        }

        // 更安全的做法
        let value = unsafe { *ptr };
        println!("✅ 更安全的指针访问: {}", value);
    }

    /// 演示正确的指针使用方式
    pub fn demonstrate_safe_pointer_usage() {
        println!("=== 安全的指针使用方式 ===");

        let mut data = vec![1, 2, 3, 4, 5];
        let ptr = data.as_mut_ptr();

        // 安全的指针操作
        unsafe {
            for i in 0..data.len() {
                let value = *ptr.add(i);
                println!("✅ 索引 {} 的值: {}", i, value);
            }
        }
    }
}

/// Rust 1.89 无效空指针参数校验演示
pub mod invalid_null_arguments_189 {

    /// 演示无效空指针参数校验
    pub fn demonstrate_invalid_null_arguments() {
        println!("=== Rust 1.89 无效空指针参数校验演示 ===");

        // 创建空指针
        let null_ptr: *const i32 = std::ptr::null();

        // 这种用法可能会触发无效空指针参数警告
        // 编译器会提醒避免传递非法空指针
        if null_ptr.is_null() {
            println!("✅ 检测到空指针，避免使用");
        }

        // 更安全的做法
        let valid_data = 42;
        let valid_ptr = &valid_data as *const i32;

        if !valid_ptr.is_null() {
            unsafe {
                let value = *valid_ptr;
                println!("✅ 通过有效指针获取值: {}", value);
            }
        }
    }

    /// 演示安全的指针参数传递
    pub fn demonstrate_safe_pointer_arguments() {
        println!("=== 安全的指针参数传递 ===");

        let data = [1, 2, 3, 4, 5];
        let ptr = data.as_ptr();

        // 安全的指针传递
        process_pointer_safely(ptr, data.len());
    }

    /// 安全处理指针的函数
    fn process_pointer_safely(ptr: *const i32, len: usize) {
        if ptr.is_null() {
            println!("❌ 接收到空指针，无法处理");
            return;
        }

        unsafe {
            for i in 0..len {
                let value = *ptr.add(i);
                println!("✅ 处理索引 {} 的值: {}", i, value);
            }
        }
    }
}

/// Rust 1.89 综合特性演示
pub struct Rust189EnhancedFeatures;

impl Rust189EnhancedFeatures {
    /// 运行所有 Rust 1.89 增强特性演示
    pub fn run_all_demonstrations() {
        println!("🚀 Rust 1.89 增强特性综合演示");
        println!("=====================================");

        // let_chains 特性演示
        let_chains_189::demonstrate_let_chains();
        let_chains_189::demonstrate_nested_let_chains();

        println!();

        // cfg_boolean_literals 特性演示
        cfg_boolean_literals_189::demonstrate_cfg_boolean_literals();

        println!();

        // 裸函数支持演示
        naked_functions_189::demonstrate_naked_functions();

        println!();

        // 危险隐式引用警告演示
        dangerous_implicit_autorefs_189::demonstrate_dangerous_implicit_autorefs();
        dangerous_implicit_autorefs_189::demonstrate_safe_pointer_usage();

        println!();

        // 无效空指针参数校验演示
        invalid_null_arguments_189::demonstrate_invalid_null_arguments();
        invalid_null_arguments_189::demonstrate_safe_pointer_arguments();

        println!();
        println!("✅ Rust 1.89 增强特性演示完成");
    }

    /// 获取 Rust 1.89 特性列表
    pub fn get_feature_list() -> Vec<&'static str> {
        vec![
            "let_chains - 在 if 和 while 条件中使用 && 操作符",
            "cfg_boolean_literals - 在条件编译中使用布尔字面量",
            "naked_functions - 裸函数支持稳定化",
            "dangerous_implicit_autorefs - 危险隐式引用警告",
            "invalid_null_arguments - 无效空指针参数校验",
        ]
    }

    /// 检查特性支持状态
    pub fn check_feature_support() -> std::collections::HashMap<String, bool> {
        let mut support_status = std::collections::HashMap::new();

        // let_chains 特性（稳定）
        support_status.insert("let_chains".to_string(), true);

        // cfg_boolean_literals 特性（稳定）
        support_status.insert("cfg_boolean_literals".to_string(), true);

        // naked_functions 特性（需要 nightly）
        support_status.insert(
            "naked_functions".to_string(),
            cfg!(all(feature = "nightly", target_arch = "x86_64")),
        );

        // dangerous_implicit_autorefs 特性（稳定）
        support_status.insert("dangerous_implicit_autorefs".to_string(), true);

        // invalid_null_arguments 特性（稳定）
        support_status.insert("invalid_null_arguments".to_string(), true);

        support_status
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_let_chains_feature() {
        // 测试 let_chains 特性
        let_chains_189::demonstrate_let_chains();
        let_chains_189::demonstrate_nested_let_chains();
    }

    #[test]
    fn test_cfg_boolean_literals_feature() {
        // 测试 cfg_boolean_literals 特性
        cfg_boolean_literals_189::demonstrate_cfg_boolean_literals();
    }

    #[test]
    fn test_feature_support_check() {
        let support_status = Rust189EnhancedFeatures::check_feature_support();

        // 检查稳定特性
        assert!(support_status.get("let_chains").unwrap_or(&false));
        assert!(support_status.get("cfg_boolean_literals").unwrap_or(&false));
        assert!(
            support_status
                .get("dangerous_implicit_autorefs")
                .unwrap_or(&false)
        );
        assert!(
            support_status
                .get("invalid_null_arguments")
                .unwrap_or(&false)
        );
    }

    #[test]
    fn test_feature_list() {
        let features = Rust189EnhancedFeatures::get_feature_list();
        assert!(!features.is_empty());
        assert!(features.len() >= 5);
    }
}
