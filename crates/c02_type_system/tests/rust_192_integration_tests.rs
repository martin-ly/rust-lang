//! # Rust 1.92.0 集成测试
//!
//! 本测试文件提供 Rust 1.92.0 特性的集成测试和端到端测试

use c02_type_system::rust_192_features::*;
use std::num::NonZeroUsize;
use std::sync::Arc;
use std::thread;

#[test]
fn test_integration_type_conversion_pipeline() {
    // 测试类型转换管道
    let converter = StringConverter;
    let inputs = vec![
        String::from("test1"),
        String::from("test2"),
        String::from("test3"),
    ];

    let outputs: Vec<String> = inputs.iter()
        .map(|input| converter.convert(input.clone()))
        .collect();

    assert_eq!(outputs.len(), 3);
    assert_eq!(outputs[0], "TEST1");
    assert_eq!(outputs[1], "TEST2");
    assert_eq!(outputs[2], "TEST3");
}

#[test]
fn test_integration_memory_management() {
    // 测试内存管理集成
    let mut manager = TypeSafeUninitManager::<i32>::new();
    assert!(!manager.is_initialized());

    manager.initialize(100);
    assert!(manager.is_initialized());

    if let Some(value) = manager.get() {
        assert_eq!(*value, 100);
    } else {
        panic!("值应该已初始化");
    }

    // 修改值
    if let Some(value) = manager.get_mut() {
        *value = 200;
    }

    assert_eq!(manager.get(), Some(&200));
}

#[test]
fn test_integration_type_size_calculation() {
    // 测试类型大小计算集成
    let calculator = TypeSizeCalculator::new(NonZeroUsize::new(8).unwrap());
    
    let sizes = vec![
        calculator.calculate_aligned::<u8>(100),
        calculator.calculate_aligned::<u16>(50),
        calculator.calculate_aligned::<u32>(25),
        calculator.calculate_aligned::<u64>(10),
    ];

    assert!(sizes[0] > 0);
    assert!(sizes[1] > 0);
    assert!(sizes[2] > 0);
    assert_eq!(sizes[3], 80); // 10 * 8
}

#[test]
fn test_integration_type_validation() {
    // 测试类型验证集成
    let validator = TypeListValidator::new(vec![1, 2, 3, 4, 5]);
    
    assert!(validator.validate(&[1, 2, 3, 4, 5]));
    assert!(!validator.validate(&[1, 2, 3, 4, 6]));
    assert!(!validator.validate(&[1, 2, 3]));
    assert!(!validator.validate(&[1, 2, 3, 4, 5, 6]));
}

#[test]
fn test_integration_concurrent_operations() {
    // 测试并发操作
    let calculator = Arc::new(TypeSizeCalculator::new(NonZeroUsize::new(8).unwrap()));
    let mut handles = vec![];

    for i in 1..=5 {
        let calc = calculator.clone();
        let handle = thread::spawn(move || {
            calc.calculate_aligned::<u64>(i * 10)
        });
        handles.push(handle);
    }

    let mut results = vec![];
    for handle in handles {
        if let Ok(size) = handle.join() {
            results.push(size);
        }
    }

    assert_eq!(results.len(), 5);
    assert_eq!(results[0], 80); // 10 * 8
    assert_eq!(results[4], 400); // 50 * 8
}

#[test]
fn test_integration_error_recovery() {
    // 测试错误恢复
    let mut manager = TypeSafeUninitManager::<String>::new();
    
    // 未初始化时应该返回 None
    assert!(manager.get().is_none());
    
    // 初始化后应该可以获取值
    manager.initialize(String::from("recovered"));
    assert!(manager.get().is_some());
    
    // 修改值
    if let Some(value) = manager.get_mut() {
        *value = String::from("modified");
    }
    
    assert_eq!(manager.get(), Some(&String::from("modified")));
}

#[test]
fn test_integration_complex_workflow() {
    // 测试复杂工作流
    // 1. 类型转换
    let converter = StringConverter;
    let input = String::from("workflow");
    let converted = converter.convert(input);
    
    // 2. 存储到未初始化管理器
    let mut manager = TypeSafeUninitManager::<String>::new();
    manager.initialize(converted);
    
    // 3. 验证存储的值
    if let Some(value) = manager.get() {
        assert_eq!(value, "WORKFLOW");
    } else {
        panic!("值应该已初始化");
    }
    
    // 4. 使用类型大小计算器
    let calculator = TypeSizeCalculator::new(NonZeroUsize::new(8).unwrap());
    let size = calculator.calculate_aligned::<String>(10);
    assert!(size > 0);
    
    // 5. 使用类型验证器
    let validator = TypeListValidator::new(vec![1, 2, 3]);
    assert!(validator.validate(&[1, 2, 3]));
}

#[test]
fn test_integration_performance_characteristics() {
    // 测试性能特征
    let converter = StringConverter;
    let large_dataset: Vec<String> = (1..=1000)
        .map(|i| format!("item_{}", i))
        .collect();

    let start = std::time::Instant::now();
    let _converted: Vec<String> = large_dataset.iter()
        .map(|s| converter.convert(s.clone()))
        .collect();
    let duration = start.elapsed();

    // 验证性能合理（应该在毫秒级别）
    assert!(duration.as_millis() < 1000);
}

#[test]
fn test_integration_edge_cases() {
    // 测试边界情况
    let calculator = TypeSizeCalculator::new(NonZeroUsize::new(8).unwrap());
    
    // 零大小
    let zero_size = calculator.calculate_aligned::<u64>(0);
    assert_eq!(zero_size, 0);
    
    // 零块
    let zero_blocks = calculator.calculate_blocks(0, NonZeroUsize::new(16).unwrap());
    assert_eq!(zero_blocks, 0);
    
    // 空列表验证
    let validator = TypeListValidator::new(vec![]);
    assert!(validator.validate(&[]));
    assert!(!validator.validate(&[1]));
}

#[test]
fn test_integration_type_safety() {
    // 测试类型安全
    let converter = StringConverter;
    let input = String::from("type_safe");
    
    // 验证输入类型满足边界约束
    let cloned = input.clone();
    let handle = thread::spawn(move || {
        converter.convert(cloned)
    });
    
    if let Ok(result) = handle.join() {
        assert_eq!(result, "TYPE_SAFE");
    } else {
        panic!("线程应该成功执行");
    }
}
