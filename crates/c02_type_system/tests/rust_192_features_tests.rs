//! # Rust 1.92.0 特性测试
//!
//! 本测试文件全面测试 Rust 1.92.0 版本的所有新特性和改进

use c02_type_system::rust_192_features::*;
use std::num::NonZeroUsize;

#[test]
fn test_type_converter_basic() {
    let converter = StringConverter;
    let input = String::from("hello");
    let output = converter.convert(input);
    assert_eq!(output, "HELLO");
}

#[test]
fn test_type_converter_generic() {
    let converter = GenericTypeConverter::<String, String>::new();
    let input = String::from("test");
    let output = converter.convert(input);
    assert_eq!(output, "test");
}

#[test]
fn test_type_converter_multiple_bounds() {
    // 测试多边界约束
    let converter = StringConverter;
    let input = String::from("multiple bounds");
    
    // 验证输入类型满足所有边界
    let cloned = input.clone();
    assert!(std::thread::spawn(move || {
        converter.convert(cloned)
    }).join().is_ok());
}

#[test]
fn test_higher_ranked_lifetimes() {
    let input = "test string";
    let result = convert_with_lifetime(input, |s| s);
    assert_eq!(result, input);
}

#[test]
fn test_process_strings() {
    let input = "processed";
    let output = process_strings(input, |s| s);
    assert_eq!(output, "processed");
}

#[test]
fn test_higher_ranked_lifetime_processor() {
    let processor = StringReverser;
    let input = "test";
    let output = processor.process(input);
    assert_eq!(output, "test");
}

#[test]
fn test_auto_trait_example() {
    let example = AutoTraitExample::new(42);
    assert_eq!(*example.get(), 42);
    
    let string_example = AutoTraitExample::new(String::from("test"));
    assert_eq!(string_example.get(), "test");
}

#[test]
fn test_auto_trait_send_sync() {
    // 测试 Send 和 Sync 自动传播
    let example = AutoTraitExample::new(42);
    
    // 验证可以跨线程传递
    let handle = std::thread::spawn(move || {
        *example.get()
    });
    
    assert_eq!(handle.join().unwrap(), 42);
}

#[test]
fn test_maybe_uninit_manager_new() {
    let manager = TypeSafeUninitManager::<i32>::new();
    assert!(!manager.is_initialized());
    assert!(manager.get().is_none());
}

#[test]
fn test_maybe_uninit_manager_initialize() {
    let mut manager = TypeSafeUninitManager::<i32>::new();
    manager.initialize(42);
    
    assert!(manager.is_initialized());
    assert_eq!(manager.get(), Some(&42));
}

#[test]
fn test_maybe_uninit_manager_get_mut() {
    let mut manager = TypeSafeUninitManager::<i32>::new();
    manager.initialize(100);
    
    if let Some(value) = manager.get_mut() {
        *value = 200;
    }
    
    assert_eq!(manager.get(), Some(&200));
}

#[test]
fn test_maybe_uninit_manager_string() {
    let mut manager = TypeSafeUninitManager::<String>::new();
    assert!(!manager.is_initialized());
    
    manager.initialize(String::from("test"));
    assert!(manager.is_initialized());
    assert_eq!(manager.get(), Some(&String::from("test")));
}

#[test]
fn test_maybe_uninit_manager_default() {
    let manager = TypeSafeUninitManager::<i32>::default();
    assert!(!manager.is_initialized());
}

#[test]
fn test_calculate_aligned_size() {
    let alignment = NonZeroUsize::new(8).unwrap();
    let size = calculate_aligned_size::<u64>(10, alignment);
    assert_eq!(size, 80); // 10 * 8, 已对齐
}

#[test]
fn test_calculate_aligned_size_zero() {
    let alignment = NonZeroUsize::new(8).unwrap();
    let size = calculate_aligned_size::<u64>(0, alignment);
    assert_eq!(size, 0);
}

#[test]
fn test_calculate_aligned_size_different_types() {
    let alignment = NonZeroUsize::new(8).unwrap();
    
    let u8_size = calculate_aligned_size::<u8>(100, alignment);
    let u16_size = calculate_aligned_size::<u16>(50, alignment);
    let u32_size = calculate_aligned_size::<u32>(25, alignment);
    let u64_size = calculate_aligned_size::<u64>(10, alignment);
    
    assert!(u8_size > 0);
    assert!(u16_size > 0);
    assert!(u32_size > 0);
    assert_eq!(u64_size, 80);
}

#[test]
fn test_type_size_calculator_new() {
    let alignment = NonZeroUsize::new(8).unwrap();
    let calculator = TypeSizeCalculator::new(alignment);
    // 测试计算功能而不是直接访问私有字段
    let size = calculator.calculate_aligned::<u64>(10);
    assert_eq!(size, 80);
}

#[test]
fn test_type_size_calculator_calculate_aligned() {
    let calculator = TypeSizeCalculator::new(NonZeroUsize::new(8).unwrap());
    let size = calculator.calculate_aligned::<u64>(10);
    assert_eq!(size, 80);
}

#[test]
fn test_type_size_calculator_calculate_blocks() {
    let calculator = TypeSizeCalculator::new(NonZeroUsize::new(8).unwrap());
    let blocks = calculator.calculate_blocks(100, NonZeroUsize::new(16).unwrap());
    assert_eq!(blocks, 7); // ceil(100/16) = 7
}

#[test]
fn test_type_size_calculator_calculate_blocks_zero() {
    let calculator = TypeSizeCalculator::new(NonZeroUsize::new(8).unwrap());
    let blocks = calculator.calculate_blocks(0, NonZeroUsize::new(16).unwrap());
    assert_eq!(blocks, 0);
}

#[test]
fn test_compare_type_lists_equal() {
    let list1 = vec![1, 2, 3, 4, 5];
    let list2 = vec![1, 2, 3, 4, 5];
    assert!(compare_type_lists(&list1, &list2));
}

#[test]
fn test_compare_type_lists_different() {
    let list1 = vec![1, 2, 3, 4, 5];
    let list2 = vec![1, 2, 3, 4, 6];
    assert!(!compare_type_lists(&list1, &list2));
}

#[test]
fn test_compare_type_lists_different_length() {
    let list1 = vec![1, 2, 3];
    let list2 = vec![1, 2, 3, 4];
    assert!(!compare_type_lists(&list1, &list2));
}

#[test]
fn test_compare_type_lists_empty() {
    let list1: Vec<i32> = vec![];
    let list2: Vec<i32> = vec![];
    assert!(compare_type_lists(&list1, &list2));
}

#[test]
fn test_compare_type_lists_strings() {
    let list1 = vec!["a", "b", "c"];
    let list2 = vec!["a", "b", "c"];
    let list3 = vec!["a", "b", "d"];
    
    assert!(compare_type_lists(&list1, &list2));
    assert!(!compare_type_lists(&list1, &list3));
}

#[test]
fn test_type_list_validator_new() {
    let validator = TypeListValidator::new(vec![1, 2, 3]);
    // 测试验证功能而不是直接访问私有字段
    assert!(validator.validate(&[1, 2, 3]));
    assert!(!validator.validate(&[1, 2, 4]));
}

#[test]
fn test_type_list_validator_validate_match() {
    let validator = TypeListValidator::new(vec![1, 2, 3]);
    assert!(validator.validate(&[1, 2, 3]));
}

#[test]
fn test_type_list_validator_validate_mismatch() {
    let validator = TypeListValidator::new(vec![1, 2, 3]);
    assert!(!validator.validate(&[1, 2, 4]));
}

#[test]
fn test_type_list_validator_validate_different_length() {
    let validator = TypeListValidator::new(vec![1, 2, 3]);
    assert!(!validator.validate(&[1, 2]));
    assert!(!validator.validate(&[1, 2, 3, 4]));
}

#[test]
fn test_type_list_validator_strings() {
    let validator = TypeListValidator::new(vec!["a", "b", "c"]);
    assert!(validator.validate(&["a", "b", "c"]));
    assert!(!validator.validate(&["a", "b", "d"]));
}

#[test]
fn test_comprehensive_demo() {
    // 运行综合演示函数
    demonstrate_rust_192_type_system_features();
}

#[test]
fn test_integration_multiple_features() {
    // 集成测试：组合多个特性
    let mut manager = TypeSafeUninitManager::<String>::new();
    let converter = StringConverter;
    let input = String::from("integration test");
    let converted = converter.convert(input);
    manager.initialize(converted);
    
    assert!(manager.is_initialized());
    if let Some(value) = manager.get() {
        assert_eq!(value, "INTEGRATION TEST");
    }
    
    // 使用类型大小计算器
    let calculator = TypeSizeCalculator::new(NonZeroUsize::new(8).unwrap());
    let size = calculator.calculate_aligned::<String>(10);
    assert!(size > 0);
    
    // 使用类型列表验证器
    let validator = TypeListValidator::new(vec![1, 2, 3]);
    assert!(validator.validate(&[1, 2, 3]));
}

#[test]
fn test_performance_characteristics() {
    // 性能特征测试
    let large_list1: Vec<i32> = (1..=10000).collect();
    let large_list2: Vec<i32> = (1..=10000).collect();
    
    let start = std::time::Instant::now();
    let result = compare_type_lists(&large_list1, &large_list2);
    let duration = start.elapsed();
    
    assert!(result);
    // 验证性能合理（应该在毫秒级别）
    assert!(duration.as_millis() < 100);
}

#[test]
fn test_edge_cases() {
    // 边界情况测试
    
    // 空字符串
    let processor = StringReverser;
    assert_eq!(processor.process(""), "");
    
    // 单个元素
    let validator = TypeListValidator::new(vec![42]);
    assert!(validator.validate(&[42]));
    assert!(!validator.validate(&[43]));
    
    // 零大小类型
    let alignment = NonZeroUsize::new(1).unwrap();
    let size = calculate_aligned_size::<()>(10, alignment);
    assert_eq!(size, 0);
}
