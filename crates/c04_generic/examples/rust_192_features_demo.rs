//! Rust 1.92.0 泛型编程特性演示示例
//!
//! 本示例展示了 Rust 1.92.0 在泛型编程场景中的新特性应用：
//! - 关联项的多个边界
//! - 增强的高阶生命周期区域处理
//! - 改进的自动特征和 Sized 边界处理
//! - 泛型约束优化
//! - NonZero::div_ceil 在泛型内存计算中的应用
//! - 迭代器方法特化
//!
//! 运行方式:
//! ```bash
//! cargo run --example rust_192_features_demo
//! ```

use c04_generic::rust_192_features::{
    GenericVector, GenericContainer, GenericTransformer, StringToNumberTransformer,
    IdentityProcessor, compose_generic_processors,
    multi_constraint_generic, ComplexConstraintGeneric,
    calculate_generic_aligned_size, GenericMemoryAllocator,
    GenericCollectionValidator,
    GenericValidator, SimpleGenericValidator, GenericResult,
    GenericFunctionComposer, GenericChainBuilder,
    GenericCache, SimpleGenericCache,
    GenericOptimizer, SimpleGenericOptimizer,
    GenericAdapter, SimpleGenericAdapter, adapt_batch,
    GenericReducer, SimpleGenericReducer,
    GenericAggregator, SimpleGenericAggregator,
    demonstrate_rust_192_generic_features,
};
use std::num::NonZeroUsize;

fn main() -> anyhow::Result<()> {
    println!("🚀 Rust 1.92.0 泛型编程特性演示\n");
    println!("{}", "=".repeat(60));

    // 使用内置的演示函数
    demonstrate_rust_192_generic_features();

    println!("\n{}", "=".repeat(60));
    println!("\n📊 实际应用场景演示\n");

    // 场景 1: 泛型容器管理
    demonstrate_generic_container_management();

    // 场景 2: 泛型转换器
    demonstrate_generic_transformer();

    // 场景 3: 泛型内存计算
    demonstrate_generic_memory_calculation();

    // 场景 4: 泛型集合验证
    demonstrate_generic_collection_validation();

    // 场景 5: 复杂泛型约束
    demonstrate_complex_generic_constraints();

    // 场景 6: 错误处理和验证
    demonstrate_error_handling_and_validation();

    // 场景 7: 泛型组合和链式操作
    demonstrate_generic_composition_and_chaining();

    // 场景 8: 泛型缓存和优化
    demonstrate_generic_cache_and_optimization();

    println!("\n✅ 所有演示完成！");

    Ok(())
}

/// 演示泛型容器管理
fn demonstrate_generic_container_management() {
    println!("\n📋 场景 1: 泛型容器管理");
    println!("{}", "-".repeat(60));

    let mut container: GenericVector<String> = GenericVector::new();

    // 添加项目
    println!("\n添加项目到容器:");
    container.set(0, String::from("item1"));
    container.set(1, String::from("item2"));
    container.set(2, String::from("item3"));

    println!("  容器大小: {}", container.size());

    // 获取项目
    println!("\n获取容器中的项目:");
    for i in 0..container.size() {
        if let Some(item) = container.get(i) {
            println!("  索引 {}: {}", i, item);
        }
    }

    // 更新项目
    println!("\n更新项目:");
    container.set(1, String::from("updated_item2"));
    if let Some(item) = container.get(1) {
        println!("  更新后的索引 1: {}", item);
    }
}

/// 演示泛型转换器
fn demonstrate_generic_transformer() {
    println!("\n\n🔄 场景 2: 泛型转换器");
    println!("{}", "-".repeat(60));

    let transformer = StringToNumberTransformer;

    println!("\n转换字符串到数字:");
    let test_cases = vec!["42", "100", "999", "invalid"];

    for case in test_cases {
        match transformer.transform(String::from(case)) {
            Ok(num) => println!("  ✓ '{}' -> {}", case, num),
            Err(e) => println!("  ✗ '{}' -> 错误: {}", case, e),
        }
    }
}

/// 演示泛型内存计算
fn demonstrate_generic_memory_calculation() {
    println!("\n\n💾 场景 3: 泛型内存计算");
    println!("{}", "-".repeat(60));

    // 计算对齐大小
    println!("\n计算泛型类型的对齐大小:");
    let alignment = NonZeroUsize::new(8).unwrap();

    let sizes = vec![
        ("u8", calculate_generic_aligned_size::<u8>(100, alignment)),
        ("u32", calculate_generic_aligned_size::<u32>(100, alignment)),
        ("u64", calculate_generic_aligned_size::<u64>(100, alignment)),
    ];

    for (type_name, size) in sizes {
        println!("  100 个 {} 对齐后大小: {} 字节", type_name, size);
    }

    // 计算内存块
    println!("\n计算内存块数:");
    let allocator = GenericMemoryAllocator::new(NonZeroUsize::new(16).unwrap());

    let blocks = vec![
        ("u32", allocator.calculate_blocks::<u32>(100)),
        ("u64", allocator.calculate_blocks::<u64>(100)),
    ];

    for (type_name, block_count) in blocks {
        println!("  100 个 {} 需要 {} 个 16 字节块", type_name, block_count);
    }
}

/// 演示泛型集合验证
fn demonstrate_generic_collection_validation() {
    println!("\n\n✅ 场景 4: 泛型集合验证");
    println!("{}", "-".repeat(60));

    let validator = GenericCollectionValidator::new(vec![1, 2, 3, 4, 5]);

    println!("\n验证集合:");
    let test_collections = vec![
        vec![1, 2, 3, 4, 5],
        vec![1, 2, 3, 4, 6],
        vec![1, 2, 3],
        vec![1, 2, 3, 4, 5, 6],
    ];

    for (i, collection) in test_collections.iter().enumerate() {
        let is_valid = validator.validate(collection);
        println!("  集合 {}: {:?} -> {}", i + 1, collection, if is_valid { "✓ 匹配" } else { "✗ 不匹配" });
    }
}

/// 演示复杂泛型约束
fn demonstrate_complex_generic_constraints() {
    println!("\n\n🔧 场景 5: 复杂泛型约束");
    println!("{}", "-".repeat(60));

    // 多约束泛型函数
    println!("\n多约束泛型函数:");
    let result: i32 = multi_constraint_generic(
        String::from("test"),
        42i32,
    );
    println!("  转换结果: {}", result);

    // 复杂约束泛型结构
    println!("\n复杂约束泛型结构:");
    let complex = ComplexConstraintGeneric::new(
        String::from("primary"),
        String::from("secondary"),
    );

    let combined = complex.combine(|p, s| format!("{} + {}", p, s));
    println!("  组合结果: {}", combined);

    // 高阶生命周期处理
    println!("\n高阶生命周期处理:");
    let processor1 = IdentityProcessor::<String>::new();
    let processor2 = IdentityProcessor::<String>::new();
    let input = String::from("test");

    let result = compose_generic_processors(&input, &processor1, &processor2);
    println!("  处理结果: {}", result);

    // 演示 ComplexConstraintGeneric 的新方法
    println!("\n复杂约束泛型结构的实用方法:");
    let mut complex = ComplexConstraintGeneric::new(
        String::from("primary"),
        String::from("secondary"),
    );
    println!("  主要值: {}", complex.primary());
    println!("  次要值: {}", complex.secondary());

    *complex.primary_mut() = String::from("updated_primary");
    println!("  更新后的主要值: {}", complex.primary());

    let swapped = complex.swapped();
    println!("  交换后的结构 - 主要值: {}, 次要值: {}", swapped.primary(), swapped.secondary());

    let tuple = swapped.into_tuple();
    println!("  转换为元组: ({}, {})", tuple.0, tuple.1);
}

/// 演示错误处理和验证
fn demonstrate_error_handling_and_validation() {
    println!("\n\n🛡️ 场景 6: 错误处理和验证");
    println!("{}", "-".repeat(60));

    // 泛型验证器
    println!("\n泛型验证器:");

    // 数字验证器
    let number_validator = SimpleGenericValidator::new(|x: &i32| *x > 0 && *x < 100);
    let numbers = vec![5, 50, 100, -1, 0];

    println!("\n验证数字 (0 < x < 100):");
    for num in numbers {
        let is_valid = GenericValidator::<i32>::validate(&number_validator, &num);
        println!("  {}: {}", num, if is_valid { "✓ 有效" } else { "✗ 无效" });
    }

    // 字符串验证器
    let string_validator = SimpleGenericValidator::new(|s: &String| s.len() >= 3 && s.len() <= 10);
    let strings = vec![
        String::from("hi"),
        String::from("test"),
        String::from("validation"),
        String::from("very_long_string"),
    ];

    println!("\n验证字符串长度 (3 <= len <= 10):");
    for s in strings {
        let is_valid = GenericValidator::<String>::validate(&string_validator, &s);
        println!("  '{}': {}", s, if is_valid { "✓ 有效" } else { "✗ 无效" });
    }

    // GenericResult 演示
    println!("\nGenericResult 类型别名:");
    let result: GenericResult<i32, String> = Ok(42);
    match result {
        Ok(value) => println!("  ✓ 成功: {}", value),
        Err(e) => println!("  ✗ 错误: {}", e),
    }

    let error_result: GenericResult<i32, String> = Err(String::from("验证失败"));
    match error_result {
        Ok(value) => println!("  ✓ 成功: {}", value),
        Err(e) => println!("  ✗ 错误: {}", e),
    }
}

/// 演示泛型组合和链式操作
fn demonstrate_generic_composition_and_chaining() {
    println!("\n\n🔗 场景 7: 泛型组合和链式操作");
    println!("{}", "-".repeat(60));

    // 泛型函数组合器
    println!("\n泛型函数组合器:");
    let composer = GenericFunctionComposer::new(
        |x: i32| x * 2,
        |x: i32| x + 1,
    );
    let result = composer.compose(5);
    println!("  组合函数 (x * 2) then (x + 1) 应用于 5: {}", result);

    // 链式泛型操作构建器
    println!("\n链式泛型操作构建器:");
    let result = GenericChainBuilder::new(10)
        .map(|x| x * 2)
        .map(|x| x + 5)
        .map(|x| x / 2)
        .unwrap();
    println!("  链式操作: 10 -> *2 -> +5 -> /2 = {}", result);

    // 使用 filter
    if let Some(builder) = GenericChainBuilder::new(15).filter(|x| *x > 10) {
        let result = builder.map(|x| x * 2).unwrap();
        println!("  过滤并映射: 15 (如果 > 10) -> *2 = {}", result);
    }

    // 使用 and_then
    let result = GenericChainBuilder::new(5)
        .and_then(|x| GenericChainBuilder::new(x * 3))
        .map(|x| x + 1)
        .unwrap();
    println!("  使用 and_then: 5 -> *3 -> +1 = {}", result);
}

/// 演示泛型缓存和优化
fn demonstrate_generic_cache_and_optimization() {
    println!("\n\n⚡ 场景 8: 泛型缓存和优化");
    println!("{}", "-".repeat(60));

    // 泛型缓存
    println!("\n泛型缓存:");
    let mut cache: SimpleGenericCache<String, i32> = SimpleGenericCache::new();

    GenericCache::<String, i32>::insert(&mut cache, String::from("key1"), 100);
    GenericCache::<String, i32>::insert(&mut cache, String::from("key2"), 200);
    GenericCache::<String, i32>::insert(&mut cache, String::from("key3"), 300);

    println!("  缓存大小: {}", GenericCache::<String, i32>::len(&cache));

    if let Some(value) = GenericCache::<String, i32>::get(&cache, &String::from("key1")) {
        println!("  获取 key1: {}", value);
    }

    let removed = GenericCache::<String, i32>::remove(&mut cache, &String::from("key2"));
    if let Some(value) = removed {
        println!("  删除 key2: {}", value);
    }

    println!("  删除后缓存大小: {}", GenericCache::<String, i32>::len(&cache));

    // 泛型优化器
    println!("\n泛型优化器:");
    let mut optimizer = SimpleGenericOptimizer::new(|x: i32| x * x); // 平方优化
    println!("  优化 5: {}", GenericOptimizer::<i32>::optimize(&mut optimizer, 5));
    println!("  优化 10: {}", GenericOptimizer::<i32>::optimize(&mut optimizer, 10));

    // 泛型适配器
    println!("\n泛型适配器:");
    let adapter = SimpleGenericAdapter::new(|x: &i32| format!("Number: {}", x));
    println!("  适配 42: {}", GenericAdapter::<i32, String>::adapt(&adapter, &42));

    let values = vec![1, 2, 3, 4, 5];
    let adapted = adapt_batch(&adapter, &values);
    println!("  批量适配: {:?}", adapted);

    // 泛型归约器
    println!("\n泛型归约器:");
    let reducer = SimpleGenericReducer::new(|values: &[i32]| values.iter().sum::<i32>());
    let values = vec![1, 2, 3, 4, 5];
    let sum = GenericReducer::<i32, i32>::reduce(&reducer, &values);
    println!("  归约求和 [1, 2, 3, 4, 5]: {}", sum);

    // 泛型聚合器
    println!("\n泛型聚合器:");
    let aggregator = SimpleGenericAggregator::new(|values: &[i32]| {
        (values.len(), values.iter().sum::<i32>(), values.iter().max().copied())
    });
    let values = vec![1, 5, 3, 9, 2];
    let (count, sum, max) = GenericAggregator::<i32, (usize, i32, Option<i32>)>::aggregate(&aggregator, &values);
    println!("  聚合结果 - 数量: {}, 总和: {}, 最大值: {:?}", count, sum, max);
}
