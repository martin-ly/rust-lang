//! # Rust 1.92.0 实用用例演示
//!
//! 本示例展示 Rust 1.92.0 特性在实际项目中的实用应用场景：
//! - 配置管理系统
//! - 数据验证管道
//! - 内存池管理
//! - 类型安全的状态机
//!
//! 运行：`cargo run --example rust_192_practical_use_cases`

use c02_type_system::rust_192_features::*;
use std::num::NonZeroUsize;
use std::collections::HashMap;

fn main() {
    println!("🦀 Rust 1.92.0 实用用例演示\n");
    println!("{}", "=".repeat(70));

    // 用例 1: 配置管理系统
    demonstrate_config_management();

    // 用例 2: 数据验证管道
    demonstrate_data_validation_pipeline();

    // 用例 3: 内存池管理
    demonstrate_memory_pool_management();

    // 用例 4: 类型安全的状态机
    demonstrate_type_safe_state_machine();

    println!("\n{}", "=".repeat(70));
    println!("✅ 所有实用用例演示完成！");
}

/// 用例 1: 配置管理系统
/// 使用关联项多边界和类型验证构建类型安全的配置系统
fn demonstrate_config_management() {
    println!("\n【用例 1: 配置管理系统】");
    println!("{}", "-".repeat(50));

    // 配置验证器
    let config_validator = TypeListValidator::new(vec![
        "database_url".to_string(),
        "api_key".to_string(),
        "timeout".to_string(),
    ]);

    // 模拟配置数据
    let valid_config = vec![
        "database_url".to_string(),
        "api_key".to_string(),
        "timeout".to_string(),
    ];

    let invalid_config = vec![
        "database_url".to_string(),
        "api_key".to_string(),
    ];

    println!("✓ 配置验证:");
    println!("  有效配置: {}", config_validator.validate(&valid_config));
    println!("  无效配置: {}", config_validator.validate(&invalid_config));

    // 配置转换器
    let converter = StringConverter;
    let mut config_map = HashMap::new();

    for key in &valid_config {
        let upper_key = converter.convert(key.clone());
        config_map.insert(upper_key, "value".to_string());
    }

    println!("\n✓ 配置转换:");
    for (key, value) in &config_map {
        println!("  {}: {}", key, value);
    }
}

/// 用例 2: 数据验证管道
/// 使用高阶生命周期和类型验证构建数据验证管道
fn demonstrate_data_validation_pipeline() {
    println!("\n【用例 2: 数据验证管道】");
    println!("{}", "-".repeat(50));

    // 创建多个验证器
    let number_validator = TypeListValidator::new(vec![1, 2, 3, 4, 5]);
    let string_validator = TypeListValidator::new(vec![
        "step1".to_string(),
        "step2".to_string(),
        "step3".to_string(),
    ]);

    // 验证数字序列
    let number_sequence = vec![1, 2, 3, 4, 5];
    println!("✓ 数字序列验证:");
    println!("  序列: {:?}", number_sequence);
    println!("  验证结果: {}", number_validator.validate(&number_sequence));

    // 验证字符串序列
    let string_sequence = vec![
        "step1".to_string(),
        "step2".to_string(),
        "step3".to_string(),
    ];
    println!("\n✓ 字符串序列验证:");
    println!("  序列: {:?}", string_sequence);
    println!("  验证结果: {}", string_validator.validate(&string_sequence));

    // 使用高阶生命周期处理字符串
    let processor = StringReverser;
    println!("\n✓ 字符串处理:");
    for step in &string_sequence {
        let processed = processor.process(step);
        println!("  \"{}\" -> \"{}\"", step, processed);
    }
}

/// 用例 3: 内存池管理
/// 使用 MaybeUninit 和类型大小计算构建高效的内存池
fn demonstrate_memory_pool_management() {
    println!("\n【用例 3: 内存池管理】");
    println!("{}", "-".repeat(50));

    // 创建内存池管理器
    let calculator = TypeSizeCalculator::new(NonZeroUsize::new(8).unwrap());

    // 计算不同类型的内存需求
    let types = vec![
        ("u8", std::mem::size_of::<u8>()),
        ("u16", std::mem::size_of::<u16>()),
        ("u32", std::mem::size_of::<u32>()),
        ("u64", std::mem::size_of::<u64>()),
    ];

    println!("✓ 类型大小计算:");
    for (name, size) in &types {
        let aligned = calculator.calculate_aligned::<u64>(100);
        println!("  {}: {} 字节, 100个元素对齐后: {} 字节", name, size, aligned);
    }

    // 使用 MaybeUninit 进行延迟初始化
    let mut pool: Vec<TypeSafeUninitManager<Vec<u8>>> = Vec::new();

    println!("\n✓ 内存池初始化:");
    for i in 0..5 {
        let mut manager = TypeSafeUninitManager::new();
        let data = vec![i; 10];
        manager.initialize(data);
        pool.push(manager);
        println!("  池项 {}: 已初始化", i);
    }

    // 访问内存池
    println!("\n✓ 内存池访问:");
    for (i, manager) in pool.iter().enumerate() {
        if let Some(data) = manager.get() {
            println!("  池项 {}: {:?}", i, &data[..5.min(data.len())]);
        }
    }
}

/// 用例 4: 类型安全的状态机
/// 使用自动特征和类型转换构建类型安全的状态机
fn demonstrate_type_safe_state_machine() {
    println!("\n【用例 4: 类型安全的状态机】");
    println!("{}", "-".repeat(50));

    // 状态定义
    #[derive(Debug, Clone, PartialEq)]
    enum State {
        Initial,
        Processing,
        Completed,
        #[allow(dead_code)]
        Error,
    }

    // 状态转换器
    struct StateConverter;

    impl TypeConverter for StateConverter {
        type Input = State;
        type Output = String;

        fn convert(&self, input: Self::Input) -> Self::Output {
            match input {
                State::Initial => "INITIAL".to_string(),
                State::Processing => "PROCESSING".to_string(),
                State::Completed => "COMPLETED".to_string(),
                State::Error => "ERROR".to_string(),
            }
        }
    }

    // 状态管理器
    let mut state_manager = TypeSafeUninitManager::<State>::new();
    let converter = StateConverter;

    // 状态转换
    let states = vec![
        State::Initial,
        State::Processing,
        State::Completed,
    ];

    println!("✓ 状态转换:");
    for state in &states {
        let state_clone = state.clone();
        state_manager.initialize(state_clone.clone());
        let state_str = converter.convert(state_clone);
        println!("  状态: {:?} -> \"{}\"", state, state_str);
    }

    // 状态验证
    let state_validator = TypeListValidator::new(vec![
        State::Initial,
        State::Processing,
        State::Completed,
    ]);

    println!("\n✓ 状态序列验证:");
    let valid_sequence = vec![
        State::Initial,
        State::Processing,
        State::Completed,
    ];
    println!("  验证结果: {}", state_validator.validate(&valid_sequence));
}
