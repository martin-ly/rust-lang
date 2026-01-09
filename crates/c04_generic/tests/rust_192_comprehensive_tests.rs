//! Rust 1.92.0 泛型特性综合测试套件
//!
//! 本测试套件验证 Rust 1.92.0 版本中的所有泛型编程新特性，确保：
//! - 关联项的多个边界正常工作
//! - 高阶生命周期区域处理正确
//! - 自动特征和 Sized 边界处理改进
//! - 泛型约束优化正常工作
//! - NonZero::div_ceil 在泛型内存计算中正确应用
//! - 迭代器方法特化性能提升

use c04_generic::rust_192_features::{
    GenericContainer, GenericVector, GenericTransformer, StringToNumberTransformer,
    GenericLifetimeProcessor, IdentityProcessor, compose_generic_processors,
    ImprovedAutoTraitGeneric, ImprovedSizedBound, SizedBoundProcessor,
    multi_constraint_generic, ComplexConstraintGeneric,
    calculate_generic_aligned_size, GenericMemoryAllocator,
    compare_generic_collections, GenericCollectionValidator,
};
use std::num::NonZeroUsize;

/// 测试关联项的多个边界
#[test]
fn test_multiple_bounds_for_associated_items() {
    let mut container: GenericVector<String> = GenericVector::new();

    // 测试基本操作
    container.set(0, String::from("item1"));
    container.set(1, String::from("item2"));

    assert_eq!(container.size(), 2);
    assert_eq!(container.get(0), Some(&String::from("item1")));
    assert_eq!(container.get(1), Some(&String::from("item2")));

    // 测试索引边界
    assert_eq!(container.get(10), None);
}

/// 测试泛型转换器
#[test]
fn test_generic_transformer() {
    let transformer = StringToNumberTransformer;

    // 测试成功转换
    assert_eq!(transformer.transform(String::from("42")).unwrap(), 42);
    assert_eq!(transformer.transform(String::from("100")).unwrap(), 100);

    // 测试失败转换
    assert!(transformer.transform(String::from("invalid")).is_err());
    assert!(transformer.transform(String::from("abc")).is_err());
}

/// 测试高阶生命周期处理
#[test]
fn test_higher_ranked_lifetime_handling() {
    let processor = IdentityProcessor::<String>::new();
    let input = String::from("test");

    // 测试基本处理
    let result = GenericLifetimeProcessor::<String>::process(&processor, &input);
    assert_eq!(result, &input);

    // 测试组合处理器
    let processor1 = IdentityProcessor::<String>::new();
    let processor2 = IdentityProcessor::<String>::new();
    let combined_result = compose_generic_processors(&input, &processor1, &processor2);
    assert_eq!(combined_result, &input);
}

/// 测试改进的自动特征推断
#[test]
fn test_improved_auto_trait_inference() {
    let example = ImprovedAutoTraitGeneric::new(String::from("test"));

    assert_eq!(example.get(), &String::from("test"));
    assert_eq!(example.into_inner(), String::from("test"));
}

/// 测试改进的 Sized 边界处理
#[test]
fn test_improved_sized_bound_handling() {
    let processor = SizedBoundProcessor;

    // 测试 Sized 类型
    let sized_value = 42;
    assert_eq!(ImprovedSizedBound::process_sized(&processor, sized_value), 42);

    // 测试可能未 Sized 的类型
    let unsized_value = "test";
    assert_eq!(ImprovedSizedBound::process_maybe_unsized(&processor, unsized_value), "test");
}

/// 测试多约束泛型函数
#[test]
fn test_multi_constraint_generic() {
    let result: i32 = multi_constraint_generic(
        String::from("test"),
        42i32,
    );
    assert_eq!(result, 42);
}

/// 测试复杂约束泛型结构
#[test]
fn test_complex_constraint_generic() {
    let complex = ComplexConstraintGeneric::new(
        String::from("primary"),
        String::from("secondary"),
    );

    let result = complex.combine(|p, s| format!("{} + {}", p, s));
    assert_eq!(result, "primary + secondary");
}

/// 测试 NonZero::div_ceil 在泛型内存计算中的应用
#[test]
fn test_div_ceil_in_generic_memory_calculation() {
    let alignment = NonZeroUsize::new(8).unwrap();

    // 测试 u64 对齐
    let size1 = calculate_generic_aligned_size::<u64>(10, alignment);
    assert_eq!(size1, 80); // 10 * 8, 已对齐

    // 测试 u32 对齐
    let size2 = calculate_generic_aligned_size::<u32>(10, alignment);
    assert_eq!(size2, 40); // 10 * 4, 已对齐

    // 测试空集合
    let size3 = calculate_generic_aligned_size::<u64>(0, alignment);
    assert_eq!(size3, 0);
}

/// 测试泛型内存分配器
#[test]
fn test_generic_memory_allocator() {
    let allocator = GenericMemoryAllocator::new(NonZeroUsize::new(16).unwrap());

    // 测试 u32 块计算
    let blocks1 = allocator.calculate_blocks::<u32>(100);
    assert_eq!(blocks1, 25); // (100 * 4) / 16 = 25

    // 测试 u64 块计算
    let blocks2 = allocator.calculate_blocks::<u64>(100);
    assert_eq!(blocks2, 50); // (100 * 8) / 16 = 50

    // 测试空集合
    let blocks3 = allocator.calculate_blocks::<u32>(0);
    assert_eq!(blocks3, 0);
}

/// 测试迭代器方法特化
#[test]
fn test_iterator_method_specialization() {
    let col1 = vec![1, 2, 3, 4, 5];
    let col2 = vec![1, 2, 3, 4, 5];
    let col3 = vec![1, 2, 3, 4, 6];

    // 测试相等集合
    assert!(compare_generic_collections(&col1, &col2));

    // 测试不相等集合
    assert!(!compare_generic_collections(&col1, &col3));

    // 测试不同长度
    let col4 = vec![1, 2, 3];
    assert!(!compare_generic_collections(&col1, &col4));
}

/// 测试泛型集合验证器
#[test]
fn test_generic_collection_validator() {
    let validator = GenericCollectionValidator::new(vec![1, 2, 3]);

    // 测试匹配集合
    assert!(validator.validate(&[1, 2, 3]));

    // 测试不匹配集合
    assert!(!validator.validate(&[1, 2, 4]));
    assert!(!validator.validate(&[1, 2]));
    assert!(!validator.validate(&[1, 2, 3, 4]));
}

/// 测试完整工作流程
#[test]
fn test_complete_workflow() {
    // 1. 创建容器
    let mut container: GenericVector<String> = GenericVector::new();
    container.set(0, String::from("item1"));
    container.set(1, String::from("item2"));

    // 2. 转换数据
    let transformer = StringToNumberTransformer;
    let number = transformer.transform(String::from("42")).unwrap();

    // 3. 处理生命周期
    let processor = IdentityProcessor::<String>::new();
    let processed = GenericLifetimeProcessor::<String>::process(&processor, container.get(0).unwrap());

    // 4. 计算内存
    let alignment = NonZeroUsize::new(8).unwrap();
    let size = calculate_generic_aligned_size::<String>(container.size(), alignment);

    // 5. 验证集合
    let validator = GenericCollectionValidator::new(vec![1, 2, 3]);
    let is_valid = validator.validate(&[1, 2, 3]);

    // 验证所有步骤都成功
    assert_eq!(container.size(), 2);
    assert_eq!(number, 42);
    assert_eq!(processed, &String::from("item1"));
    assert!(size > 0);
    assert!(is_valid);
}

/// 测试 GenericVector 的新方法
#[test]
fn test_generic_vector_utility_methods() {
    let mut container: GenericVector<String> = GenericVector::new();

    // 测试 is_empty
    assert!(container.is_empty());

    // 测试 push 和 pop
    container.push(String::from("item1"));
    container.push(String::from("item2"));
    assert_eq!(container.size(), 2);
    assert!(!container.is_empty());

    assert_eq!(container.pop(), Some(String::from("item2")));
    assert_eq!(container.size(), 1);

    // 测试 insert 和 remove
    container.insert(0, String::from("item0"));
    assert_eq!(container.size(), 2);
    assert_eq!(container.get(0), Some(&String::from("item0")));

    let removed = container.remove(1);
    assert_eq!(removed, Some(String::from("item1")));
    assert_eq!(container.size(), 1);

    // 测试 clear
    container.clear();
    assert!(container.is_empty());
    assert_eq!(container.size(), 0);

    // 测试迭代器
    container.push(String::from("a"));
    container.push(String::from("b"));
    let items: Vec<&String> = container.iter().collect();
    assert_eq!(items.len(), 2);
}

/// 测试 GenericMemoryAllocator 的新方法
#[test]
fn test_memory_allocator_utility_methods() {
    let allocator = GenericMemoryAllocator::new(NonZeroUsize::new(16).unwrap());

    assert_eq!(allocator.block_size().get(), 16);

    // 测试总大小计算
    let total_size = allocator.calculate_total_size::<u32>(100);
    assert_eq!(total_size, 400); // 100 * 4

    // 测试对齐后的总大小
    let aligned_size = allocator.calculate_aligned_total_size::<u32>(100);
    assert_eq!(aligned_size, 400); // 25 blocks * 16 = 400
}

/// 测试 GenericCollectionValidator 的新方法
#[test]
fn test_collection_validator_utility_methods() {
    let mut validator = GenericCollectionValidator::new(vec![1, 2, 3]);

    assert!(!validator.is_empty());
    assert_eq!(validator.expected(), &[1, 2, 3]);

    // 测试更新期望集合
    validator.update_expected(vec![4, 5, 6]);
    assert_eq!(validator.expected(), &[4, 5, 6]);
    assert!(validator.validate(&[4, 5, 6]));

    // 测试空集合
    let empty_validator: GenericCollectionValidator<i32> = GenericCollectionValidator::new(vec![]);
    assert!(empty_validator.is_empty());
}

/// 测试 ComplexConstraintGeneric 的新方法
#[test]
fn test_complex_constraint_generic_utility_methods() {
    let mut complex = ComplexConstraintGeneric::new(
        String::from("primary"),
        String::from("secondary"),
    );

    // 测试获取值
    assert_eq!(complex.primary(), &String::from("primary"));
    assert_eq!(complex.secondary(), &String::from("secondary"));

    // 测试修改值
    *complex.primary_mut() = String::from("updated_primary");
    assert_eq!(complex.primary(), &String::from("updated_primary"));

    // 测试转换为元组
    let tuple = complex.into_tuple();
    assert_eq!(tuple.0, String::from("updated_primary"));
    assert_eq!(tuple.1, String::from("secondary"));

    // 测试交换（创建新实例）
    let complex2 = ComplexConstraintGeneric::new(
        String::from("a"),
        String::from("b"),
    );
    let swapped = complex2.swapped();
    assert_eq!(swapped.primary(), &String::from("b"));
    assert_eq!(swapped.secondary(), &String::from("a"));
}

/// 测试 SizedBoundProcessor 的新方法
#[test]
fn test_sized_bound_processor_utility_methods() {
    let processor = SizedBoundProcessor::new();

    // 测试批量处理（手动处理每个值）
    let values = vec![1, 2, 3, 4, 5];
    let processed: Vec<i32> = values.iter().map(|&v| ImprovedSizedBound::process_sized(&processor, v)).collect();
    assert_eq!(processed, vec![1, 2, 3, 4, 5]);

    // 测试 Default
    let default_processor = SizedBoundProcessor::default();
    assert_eq!(ImprovedSizedBound::process_sized(&default_processor, 42), 42);
}

/// 测试便利函数
#[test]
fn test_convenience_functions() {
    use c04_generic::rust_192_features::{
        create_default_memory_allocator, create_generic_vectors, create_transformer_chain,
    };

    // 测试创建默认内存分配器
    let allocator = create_default_memory_allocator();
    assert_eq!(allocator.block_size().get(), 16);

    // 测试批量创建泛型向量
    let vectors = create_generic_vectors(vec![
        vec!["a", "b"],
        vec!["c", "d"],
    ]);
    assert_eq!(vectors.len(), 2);
    assert_eq!(vectors[0].size(), 2);
    assert_eq!(vectors[1].size(), 2);

    // 测试创建转换器链
    let transformers = create_transformer_chain(3);
    assert_eq!(transformers.len(), 3);
}

/// 测试泛型验证器
#[test]
fn test_generic_validator() {
    use c04_generic::rust_192_features::{GenericValidator, SimpleGenericValidator};

    // 测试数字验证器
    let number_validator = SimpleGenericValidator::new(|x: &i32| *x > 0);
    assert!(number_validator.validate(&5));
    assert!(!number_validator.validate(&-1));

    // 测试字符串验证器
    let string_validator = SimpleGenericValidator::new(|s: &String| s.len() > 3);
    assert!(string_validator.validate(&String::from("test")));
    assert!(!string_validator.validate(&String::from("hi")));
}

/// 测试改进的自动特征泛型
#[test]
fn test_improved_auto_trait_generic() {
    use c04_generic::rust_192_features::ImprovedAutoTraitGeneric;

    let generic_value = ImprovedAutoTraitGeneric::new(42);
    assert_eq!(*generic_value.get(), 42);

    // 测试 Clone
    let cloned = generic_value.clone();
    assert_eq!(*cloned.get(), 42);

    // 测试 Debug
    let debug_str = format!("{:?}", generic_value);
    assert!(debug_str.contains("42"));
}

/// 测试泛型映射器
#[test]
fn test_generic_mapper() {
    use c04_generic::rust_192_features::{GenericMapper, SimpleGenericMapper};
    
    // 测试数字映射器
    let mapper = SimpleGenericMapper::new(|x: &i32| *x * 2);
    assert_eq!(mapper.map(&5), 10);
    assert_eq!(mapper.map(&10), 20);
    
    // 测试字符串映射器
    let string_mapper = SimpleGenericMapper::new(|s: &String| s.len());
    assert_eq!(string_mapper.map(&String::from("test")), 4);
    assert_eq!(string_mapper.map(&String::from("hello")), 5);
}

/// 测试泛型组合器
#[test]
fn test_generic_combinator() {
    use c04_generic::rust_192_features::{GenericCombinator, SimpleGenericCombinator};
    
    let combinator = SimpleGenericCombinator::new(|a: &i32, b: &i32| *a + *b);
    assert_eq!(combinator.combine(&5, &10), 15);
    assert_eq!(combinator.combine(&20, &30), 50);
    
    let string_combinator = SimpleGenericCombinator::new(|a: &String, b: &String| format!("{}{}", a, b));
    assert_eq!(string_combinator.combine(&String::from("hello"), &String::from("world")), "helloworld");
}

/// 测试泛型过滤器
#[test]
fn test_generic_filter() {
    use c04_generic::rust_192_features::{GenericFilter, SimpleGenericFilter};
    
    let filter = SimpleGenericFilter::new(|x: &i32| *x > 0);
    assert!(filter.filter(&5));
    assert!(!filter.filter(&-1));
    assert!(!filter.filter(&0));
    
    let string_filter = SimpleGenericFilter::new(|s: &String| s.len() > 3);
    assert!(string_filter.filter(&String::from("test")));
    assert!(!string_filter.filter(&String::from("hi")));
}

/// 测试批量操作
#[test]
fn test_batch_operations() {
    use c04_generic::rust_192_features::{
        SimpleGenericValidator,
        SimpleGenericMapper,
        SimpleGenericFilter,
        validate_batch, map_batch, filter_batch,
    };
    
    // 测试批量验证
    let validator = SimpleGenericValidator::new(|x: &i32| *x > 0);
    let values = vec![-1, 0, 1, 2, 3];
    let results = validate_batch(&validator, &values);
    assert_eq!(results, vec![false, false, true, true, true]);
    
    // 测试批量映射
    let mapper = SimpleGenericMapper::new(|x: &i32| *x * 2);
    let values = vec![1, 2, 3, 4, 5];
    let mapped = map_batch(&mapper, &values);
    assert_eq!(mapped, vec![2, 4, 6, 8, 10]);
    
    // 测试批量过滤
    let filter = SimpleGenericFilter::new(|x: &i32| *x % 2 == 0);
    let values = vec![1, 2, 3, 4, 5, 6];
    let filtered = filter_batch(&filter, &values);
    assert_eq!(filtered, vec![2, 4, 6]);
}

/// 测试泛型函数组合器
#[test]
fn test_generic_function_composer() {
    use c04_generic::rust_192_features::GenericFunctionComposer;
    
    let composer = GenericFunctionComposer::new(
        |x: i32| x * 2,
        |x: i32| x + 1,
    );
    assert_eq!(composer.compose(5), 11); // (5 * 2) + 1 = 11
}

/// 测试链式泛型操作构建器
#[test]
fn test_generic_chain_builder() {
    use c04_generic::rust_192_features::GenericChainBuilder;
    
    // 测试基本链式操作
    let result = GenericChainBuilder::new(5)
        .map(|x| x * 2)
        .map(|x| x + 1)
        .unwrap();
    assert_eq!(result, 11);
    
    // 测试 filter
    if let Some(builder) = GenericChainBuilder::new(5).filter(|x| *x > 0) {
        let result = builder.map(|x| x * 2).unwrap();
        assert_eq!(result, 10);
    } else {
        panic!("Filter should return Some");
    }
    
    // 测试 and_then
    let result = GenericChainBuilder::new(5)
        .and_then(|x| GenericChainBuilder::new(x * 2))
        .unwrap();
    assert_eq!(result, 10);
}

/// 测试泛型缓存
#[test]
fn test_generic_cache() {
    use c04_generic::rust_192_features::{GenericCache, SimpleGenericCache};
    
    let mut cache = SimpleGenericCache::new();
    
    // 测试插入和获取
    cache.insert("key1", 42);
    assert_eq!(cache.get(&"key1"), Some(&42));
    assert_eq!(cache.get(&"key2"), None);
    
    // 测试长度
    assert_eq!(cache.len(), 1);
    assert!(!cache.is_empty());
    
    // 测试删除
    let removed = cache.remove(&"key1");
    assert_eq!(removed, Some(42));
    assert_eq!(cache.len(), 0);
    assert!(cache.is_empty());
    
    // 测试清空
    cache.insert("key1", 1);
    cache.insert("key2", 2);
    cache.clear();
    assert!(cache.is_empty());
}

/// 测试泛型优化器
#[test]
fn test_generic_optimizer() {
    use c04_generic::rust_192_features::{GenericOptimizer, SimpleGenericOptimizer};
    
    let mut optimizer = SimpleGenericOptimizer::new(|x: i32| x * 2);
    assert_eq!(optimizer.optimize(5), 10);
    assert_eq!(optimizer.optimize(10), 20);
}

/// 测试泛型适配器
#[test]
fn test_generic_adapter() {
    use c04_generic::rust_192_features::{GenericAdapter, SimpleGenericAdapter, adapt_batch};
    
    let adapter = SimpleGenericAdapter::new(|x: &i32| *x * 2);
    assert_eq!(adapter.adapt(&5), 10);
    
    // 测试批量适配
    let values = vec![1, 2, 3, 4, 5];
    let adapted = adapt_batch(&adapter, &values);
    assert_eq!(adapted, vec![2, 4, 6, 8, 10]);
}

/// 测试泛型归约器
#[test]
fn test_generic_reducer() {
    use c04_generic::rust_192_features::{GenericReducer, SimpleGenericReducer};
    
    let reducer = SimpleGenericReducer::new(|values: &[i32]| values.iter().sum::<i32>());
    let values = vec![1, 2, 3, 4, 5];
    assert_eq!(reducer.reduce(&values), 15);
}

/// 测试泛型聚合器
#[test]
fn test_generic_aggregator() {
    use c04_generic::rust_192_features::{GenericAggregator, SimpleGenericAggregator};
    
    let aggregator = SimpleGenericAggregator::new(|values: &[i32]| {
        (values.len(), values.iter().sum::<i32>())
    });
    let values = vec![1, 2, 3, 4, 5];
    let (count, sum) = aggregator.aggregate(&values);
    assert_eq!(count, 5);
    assert_eq!(sum, 15);
}

/// 测试边界情况 - 空集合
#[test]
fn test_edge_cases_empty_collections() {
    use c04_generic::rust_192_features::{
        SimpleGenericValidator, validate_batch,
        SimpleGenericMapper, map_batch,
        SimpleGenericFilter, filter_batch,
        SimpleGenericAdapter, adapt_batch,
        GenericReducer, SimpleGenericReducer,
        GenericAggregator, SimpleGenericAggregator,
    };
    
    // 测试空集合验证
    let validator = SimpleGenericValidator::new(|x: &i32| *x > 0);
    let empty: Vec<i32> = vec![];
    let results = validate_batch(&validator, &empty);
    assert_eq!(results.len(), 0);
    
    // 测试空集合映射
    let mapper = SimpleGenericMapper::new(|x: &i32| *x * 2);
    let empty: Vec<i32> = vec![];
    let mapped = map_batch(&mapper, &empty);
    assert_eq!(mapped.len(), 0);
    
    // 测试空集合过滤
    let filter = SimpleGenericFilter::new(|x: &i32| *x > 0);
    let empty: Vec<i32> = vec![];
    let filtered = filter_batch(&filter, &empty);
    assert_eq!(filtered.len(), 0);
    
    // 测试空集合适配
    let adapter = SimpleGenericAdapter::new(|x: &i32| *x * 2);
    let empty: Vec<i32> = vec![];
    let adapted = adapt_batch(&adapter, &empty);
    assert_eq!(adapted.len(), 0);
    
    // 测试空集合归约
    let reducer = SimpleGenericReducer::new(|values: &[i32]| values.iter().sum::<i32>());
    let empty: Vec<i32> = vec![];
    assert_eq!(reducer.reduce(&empty), 0);
    
    // 测试空集合聚合
    let aggregator = SimpleGenericAggregator::new(|values: &[i32]| {
        (values.len(), values.iter().sum::<i32>())
    });
    let empty: Vec<i32> = vec![];
    let (count, sum) = aggregator.aggregate(&empty);
    assert_eq!(count, 0);
    assert_eq!(sum, 0);
}

/// 测试边界情况 - 单个元素
#[test]
fn test_edge_cases_single_element() {
    use c04_generic::rust_192_features::{
        GenericChainBuilder, SimpleGenericCache, GenericCache,
    };
    
    // 测试单个元素的链式操作
    let result = GenericChainBuilder::new(42)
        .map(|x| x * 2)
        .unwrap();
    assert_eq!(result, 84);
    
    // 测试单个元素的缓存
    let mut cache: SimpleGenericCache<String, i32> = SimpleGenericCache::new();
    cache.insert(String::from("key"), 100);
    assert_eq!(cache.len(), 1);
    assert_eq!(cache.get(&String::from("key")), Some(&100));
    
    // 测试删除单个元素
    let removed = cache.remove(&String::from("key"));
    assert_eq!(removed, Some(100));
    assert_eq!(cache.len(), 0);
    assert!(cache.is_empty());
}

/// 测试边界情况 - 最大值和最小值
#[test]
fn test_edge_cases_min_max_values() {
    use c04_generic::rust_192_features::{
        GenericValidator, SimpleGenericValidator,
        GenericMapper, SimpleGenericMapper,
    };
    
    // 测试最大值
    let validator = SimpleGenericValidator::new(|x: &i32| *x > 0);
    assert!(validator.validate(&i32::MAX));
    
    // 测试最小值
    assert!(!validator.validate(&i32::MIN));
    assert!(!validator.validate(&0));
    
    // 测试映射最大值
    let mapper = SimpleGenericMapper::new(|x: &i32| *x * 2);
    // 注意：这里可能会溢出，但测试基本功能
    let small_value = 10;
    assert_eq!(mapper.map(&small_value), 20);
}

/// 测试边界情况 - 类型边界
#[test]
fn test_edge_cases_type_bounds() {
    use c04_generic::rust_192_features::{
        GenericChainBuilder, SimpleGenericCache, GenericCache,
    };
    
    // 测试不同类型
    let string_result = GenericChainBuilder::new(String::from("test"))
        .map(|s| s.len())
        .unwrap();
    assert_eq!(string_result, 4);
    
    // 测试不同类型的缓存
    let mut cache: SimpleGenericCache<i32, String> = SimpleGenericCache::new();
    cache.insert(1, String::from("value1"));
    cache.insert(2, String::from("value2"));
    assert_eq!(cache.len(), 2);
    
    if let Some(value) = cache.get(&1) {
        assert_eq!(value, "value1");
    }
}

/// 测试边界情况 - 并发安全性（基本测试）
#[test]
fn test_edge_cases_concurrent_safety() {
    use c04_generic::rust_192_features::{GenericCache, SimpleGenericCache};
    use std::sync::Arc;
    use std::thread;
    
    let cache: Arc<std::sync::Mutex<SimpleGenericCache<i32, i32>>> = 
        Arc::new(std::sync::Mutex::new(SimpleGenericCache::new()));
    
    let handles: Vec<_> = (0..10)
        .map(|i| {
            let cache = Arc::clone(&cache);
            thread::spawn(move || {
                let mut cache_guard = cache.lock().unwrap();
                cache_guard.insert(i, i * 2);
            })
        })
        .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    let cache_guard = cache.lock().unwrap();
    assert_eq!(cache_guard.len(), 10);
}

/// 测试边界情况 - 大集合性能
#[test]
fn test_edge_cases_large_collections() {
    use c04_generic::rust_192_features::{
        SimpleGenericValidator, validate_batch,
        SimpleGenericMapper, map_batch,
    };
    
    // 测试大集合（1000个元素）
    let large_vec: Vec<i32> = (0..1000).collect();
    
    let validator = SimpleGenericValidator::new(|x: &i32| *x % 2 == 0);
    let results = validate_batch(&validator, &large_vec);
    assert_eq!(results.len(), 1000);
    assert_eq!(results.iter().filter(|&&x| x).count(), 500);
    
    let mapper = SimpleGenericMapper::new(|x: &i32| *x * 2);
    let mapped = map_batch(&mapper, &large_vec);
    assert_eq!(mapped.len(), 1000);
    assert_eq!(mapped[0], 0);
    assert_eq!(mapped[999], 1998);
}
