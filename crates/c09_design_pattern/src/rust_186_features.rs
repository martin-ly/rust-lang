//! Rust 186.0 新特性实现模块 —— c09_design_pattern
//!
//! 本模块展示了 Rust 186.0 (2025-04-03) 的关键语言特性和工具链改进。
//! This module demonstrates key language features and toolchain improvements of Rust 186.0 (2025-04-03).
//!
//! - `trait_upcasting`: Trait 对象向上转换（dyn Trait + Trait -> dyn Trait）
//! - `trait_upcasting`: Trait object upcasting (dyn Trait + Trait -> dyn Trait)
//! # this
//! - Rust 版本: 186.0
//! - Rust Version: 186.0
//! - 稳定日期: 2025-04-03
//! - Stable Date: 2025-04-03
//! - Edition: 2024

// ============================================================================
// 1. Trait 对象向上转换（dyn Trait + Trait -> dyn Trait）
// ============================================================================

/// # Trait 对象向上转换
/// # Trait Object Upcasting
///
/// Rust 1.86.0 稳定了 trait 对象的向上转换（upcasting）：
/// Rust 1.86.0 trait to on conversion （upcasting）：
/// 可以将 `dyn SubTrait` 转换为 `dyn SuperTrait`。
///
/// ## 使用场景
/// ## Usage Scenarios
/// - 抽象层解耦：在运行时根据具体类型降级到更通用的 trait 对象
/// - Abstraction decoupling: downgrade to more general trait objects at runtime based on specific types
/// - 插件系统：将特定插件接口转换为通用接口
/// - Plugin system: convert specific plugin interfaces to general interfaces
pub trait Animal {
    fn name(&self) -> &'static str;
}
pub trait Dog: Animal {
    fn bark(&self);
}

pub fn animal_name(animal: &dyn Animal) -> &'static str {
    animal.name()
}

#[cfg(test)]
mod tests {
    use super::*;
    struct MyDog;
    impl Animal for MyDog {
        fn name(&self) -> &'static str {
            "Buddy"
        }
    }
    impl Dog for MyDog {
        fn bark(&self) {}
    }

    #[test]
    fn test_trait_upcasting() {
        let dog: &dyn Dog = &MyDog;
        // 1.86+: 可以直接将 dyn Dog 转换为 dyn Animal
        let animal: &dyn Animal = dog;
        assert_eq!(animal.name(), "Buddy");
    }
}
