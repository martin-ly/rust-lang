//! Rust 1.92.0 宏系统新特性演示程序
//!
//! 这个程序展示了如何在 c11_macro_system 项目中使用最新的 Rust 1.92.0 特性
use c11_macro_system::rust_192_features::{
    demonstrate_rust_192_macro_features,
    MacroExpansionQueue, MacroExpansionItem,
    calculate_macro_cache_size, MacroMemoryAllocator,
    compare_macro_lists, check_macro_expansion_states,
    MacroExpansionPerformanceMonitor,
};
use std::num::NonZeroUsize;

fn main() {
    println!("🚀 Rust 1.92.0 宏系统新特性演示");
    println!("=================================\n");

    // 运行综合演示
    demonstrate_rust_192_macro_features();

    // 额外演示：宏展开队列管理
    println!("\n=== 额外演示：宏展开队列管理 ===");
    let mut queue = MacroExpansionQueue::new();

    // 添加宏展开项
    queue.push(MacroExpansionItem {
        name: "derive_debug".to_string(),
        priority: 10,
        depth: 1,
    });
    queue.push(MacroExpansionItem {
        name: "derive_clone".to_string(),
        priority: 20,
        depth: 2,
    });
    queue.push(MacroExpansionItem {
        name: "derive_serialize".to_string(),
        priority: 30,
        depth: 3,
    });
    queue.push(MacroExpansionItem {
        name: "custom_macro".to_string(),
        priority: 40,
        depth: 4,
    });

    println!("初始队列顺序:");
    for (i, item) in queue.iter().enumerate() {
        println!("  {}: Name={}, Priority={}, Depth={}",
            i + 1, item.name, item.priority, item.depth);
    }

    // 轮转队列
    queue.rotate(2);
    println!("\n轮转 2 个位置后:");
    for (i, item) in queue.iter().enumerate() {
        println!("  {}: Name={}, Priority={}, Depth={}",
            i + 1, item.name, item.priority, item.depth);
    }

    // 额外演示：宏缓存大小计算
    println!("\n=== 额外演示：宏缓存大小计算 ===");
    let macros_per_entry = NonZeroUsize::new(15).unwrap();
    let total_macros = vec!["macro1", "macro2", "macro3", "macro4", "macro5"];
    let cache_size = calculate_macro_cache_size(total_macros.len(), macros_per_entry);
    println!("总宏数: {}", total_macros.len());
    println!("每缓存条目宏数: {}", macros_per_entry);
    println!("需要的缓存条目数: {}", cache_size);

    // 额外演示：内存分配
    println!("\n=== 额外演示：宏展开内存分配 ===");
    let allocator = MacroMemoryAllocator::new(2048, NonZeroUsize::new(64).unwrap());
    println!("总内存: 2048 KB");
    println!("每宏内存: 64 KB");
    println!("最大宏数: {}", allocator.max_macros());

    // 额外演示：宏列表比较
    println!("\n=== 额外演示：宏列表比较 ===");
    let list1 = vec![
        MacroExpansionItem {
            name: "macro_a".to_string(),
            priority: 50,
            depth: 1,
        },
        MacroExpansionItem {
            name: "macro_b".to_string(),
            priority: 60,
            depth: 2,
        },
    ];
    let list2 = list1.clone();
    let list3 = vec![
        MacroExpansionItem {
            name: "macro_a".to_string(),
            priority: 50,
            depth: 1,
        },
        MacroExpansionItem {
            name: "macro_c".to_string(),
            priority: 70,
            depth: 3,
        },
    ];

    println!("列表1 和 列表2 相等: {}", compare_macro_lists(&list1, &list2));
    println!("列表1 和 列表3 相等: {}", compare_macro_lists(&list1, &list3));

    // 额外演示：宏展开状态检查
    println!("\n=== 额外演示：宏展开状态检查 ===");
    let macros = vec![
        MacroExpansionItem {
            name: "test_macro_1".to_string(),
            priority: 80,
            depth: 1,
        },
        MacroExpansionItem {
            name: "test_macro_2".to_string(),
            priority: 90,
            depth: 2,
        },
    ];
    let expected_names = vec!["test_macro_1".to_string(), "test_macro_2".to_string()];
    let wrong_names = vec!["test_macro_1".to_string(), "test_macro_3".to_string()];

    println!("宏列表匹配预期名称: {}",
        check_macro_expansion_states(&macros, &expected_names));
    println!("宏列表匹配错误名称: {}",
        check_macro_expansion_states(&macros, &wrong_names));

    // 额外演示：性能监控
    println!("\n=== 额外演示：宏展开性能监控 ===");
    let mut monitor = MacroExpansionPerformanceMonitor::new();

    // 模拟一些宏展开
    monitor.record_expansion(120);
    monitor.record_expansion(150);
    monitor.record_expansion(130);
    monitor.record_expansion(140);
    monitor.record_expansion(125);

    // 模拟缓存命中/未命中
    monitor.record_cache_hit();
    monitor.record_cache_hit();
    monitor.record_cache_hit();
    monitor.record_cache_miss();
    monitor.record_cache_miss();

    if let Some(avg) = monitor.average_expansion_time() {
        println!("平均展开时间: {:.2} ns", avg);
    }
    println!("缓存命中率: {:.2}%", monitor.cache_hit_rate() * 100.0);
    println!("总展开次数: {}", monitor.expansion_count());
    println!("缓存命中: {}", monitor.cache_hits());
    println!("缓存未命中: {}", monitor.cache_misses());

    println!("\n✅ 所有演示完成！");
}
