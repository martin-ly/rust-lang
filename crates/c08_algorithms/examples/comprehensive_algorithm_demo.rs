//! 综合算法演示程序
//! 
//! 本程序展示了 c08_algorithms 库中各种算法的使用方法，
//! 包括同步、异步、并行三种实现方式的对比。
//!
//! ## 📐 知识结构
//!
//! ### 核心概念
//!
//! - **算法演示**: 展示各种算法的使用方法和性能对比
//!   - **属性**: 排序、搜索、图算法、动态规划、分治、字符串算法
//!   - **关系**: 与算法、数据结构、性能分析相关
//!
//! ### 思维导图
//!
//! ```text
//! 综合算法演示
//! │
//! ├── 排序算法
//! │   ├── 同步排序
//! │   ├── 并行排序
//! │   └── 异步排序
//! ├── 搜索算法
//! │   ├── 线性搜索
//! │   └── 二分搜索
//! ├── 图算法
//! │   ├── BFS
//! │   └── Dijkstra
//! ├── 动态规划
//! │   ├── LCS
//! │   └── 背包问题
//! └── 字符串算法
//!     ├── KMP
//!     └── Rabin-Karp
//! ```

use c08_algorithms::{
    sorting::{sort_sync, sort_parallel, sort_async, SortingAlgo},
    searching::{linear_search_sync, binary_search_sync, parallel_search, linear_search_async, binary_search_async},
    graph::{bfs_shortest_path_sync, dijkstra_sync, bfs_shortest_path_async, dijkstra_async},
    dynamic_programming::{lcs_sync, knapsack_01_sync, lis_length_sync, lcs_async, knapsack_01_async},
    divide_and_conquer::{max_subarray_sum_sync, closest_pair_sync, fast_pow_mod, max_subarray_sum_async, closest_pair_async},
    string_algorithms::{kmp_search, rabin_karp_search, manacher_longest_palindrome, kmp_search_async, rabin_karp_search_async},
    backtracking::{nqueens_solutions_sync, permutations_sync, subsets_sync, nqueens_solutions_async, permutations_async, subsets_async},
    greedy::{interval_scheduling_sync, coin_change_greedy_sync, fractional_knapsack_sync, interval_scheduling_async, coin_change_greedy_async},
};
use std::collections::HashMap;
use std::time::Instant;

/// 演示排序算法
async fn demo_sorting_algorithms() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 排序算法演示 ===");
    
    // 生成测试数据
    let mut data = vec![64, 34, 25, 12, 22, 11, 90, 5, 77, 30];
    println!("原始数据: {:?}", data);
    
    // 同步排序
    let start = Instant::now();
    sort_sync(&mut data, SortingAlgo::Quick);
    println!("同步快速排序: {:?} (耗时: {:?})", data, start.elapsed());
    
    // 并行排序
    let mut data = vec![64, 34, 25, 12, 22, 11, 90, 5, 77, 30];
    let start = Instant::now();
    sort_parallel(&mut data, SortingAlgo::Merge);
    println!("并行归并排序: {:?} (耗时: {:?})", data, start.elapsed());
    
    // 异步排序
    let data = vec![64, 34, 25, 12, 22, 11, 90, 5, 77, 30];
    let start = Instant::now();
    let sorted = sort_async(data, SortingAlgo::Heap).await?;
    println!("异步堆排序: {:?} (耗时: {:?})", sorted, start.elapsed());
    
    Ok(())
}

/// 演示搜索算法
async fn demo_searching_algorithms() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 搜索算法演示 ===");
    
    let data = vec![1, 3, 5, 7, 9, 11, 13, 15, 17, 19];
    let target = 11;
    println!("在数据 {:?} 中搜索 {}", data, target);
    
    // 同步线性搜索
    let start = Instant::now();
    let pos = linear_search_sync(&data, &target);
    println!("同步线性搜索: {:?} (耗时: {:?})", pos, start.elapsed());
    
    // 并行搜索
    let start = Instant::now();
    let pos = parallel_search(&data, &target);
    println!("并行搜索: {:?} (耗时: {:?})", pos, start.elapsed());
    
    // 同步二分搜索
    let start = Instant::now();
    let pos = binary_search_sync(&data, &target)?;
    println!("同步二分搜索: {:?} (耗时: {:?})", pos, start.elapsed());
    
    // 异步线性搜索
    let start = Instant::now();
    let pos = linear_search_async(data.clone(), target).await?;
    println!("异步线性搜索: {:?} (耗时: {:?})", pos, start.elapsed());
    
    // 异步二分搜索
    let start = Instant::now();
    let pos = binary_search_async(data, target).await?;
    println!("异步二分搜索: {:?} (耗时: {:?})", pos, start.elapsed());
    
    Ok(())
}

/// 演示图算法
async fn demo_graph_algorithms() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 图算法演示 ===");
    
    // 构建测试图
    let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
    graph.insert(1, vec![2, 3]);
    graph.insert(2, vec![4, 5]);
    graph.insert(3, vec![4]);
    graph.insert(4, vec![6]);
    graph.insert(5, vec![6]);
    graph.insert(6, vec![]);
    
    println!("图结构: {:?}", graph);
    
    // 同步BFS
    let start = Instant::now();
    let path = bfs_shortest_path_sync(&graph, &1, &6);
    println!("同步BFS最短路径: {:?} (耗时: {:?})", path, start.elapsed());
    
    // 异步BFS
    let start = Instant::now();
    let path = bfs_shortest_path_async(graph.clone(), 1, 6).await?;
    println!("异步BFS最短路径: {:?} (耗时: {:?})", path, start.elapsed());
    
    // 构建加权图
    let mut weighted_graph: HashMap<&str, Vec<(&str, f64)>> = HashMap::new();
    weighted_graph.insert("A", vec![("B", 1.0), ("C", 4.0)]);
    weighted_graph.insert("B", vec![("C", 2.0), ("D", 5.0)]);
    weighted_graph.insert("C", vec![("D", 1.0)]);
    weighted_graph.insert("D", vec![]);
    
    println!("加权图: {:?}", weighted_graph);
    
    // 同步Dijkstra
    let start = Instant::now();
    let (distances, _predecessors) = dijkstra_sync(&weighted_graph, &"A");
    println!("同步Dijkstra距离: {:?} (耗时: {:?})", distances, start.elapsed());
    
    // 异步Dijkstra
    let start = Instant::now();
    let (distances, _predecessors) = dijkstra_async(weighted_graph, "A").await?;
    println!("异步Dijkstra距离: {:?} (耗时: {:?})", distances, start.elapsed());
    
    Ok(())
}

/// 演示动态规划算法
async fn demo_dynamic_programming_algorithms() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 动态规划算法演示 ===");
    
    // 最长公共子序列
    let seq1 = b"ABCBDAB";
    let seq2 = b"BDCABA";
    println!("序列1: {:?}", String::from_utf8_lossy(seq1));
    println!("序列2: {:?}", String::from_utf8_lossy(seq2));
    
    let start = Instant::now();
    let lcs_len = lcs_sync(seq1, seq2);
    println!("同步LCS长度: {} (耗时: {:?})", lcs_len, start.elapsed());
    
    let start = Instant::now();
    let lcs_len = lcs_async(seq1.to_vec(), seq2.to_vec()).await?;
    println!("异步LCS长度: {} (耗时: {:?})", lcs_len, start.elapsed());
    
    // 0-1背包问题
    let weights = vec![2, 3, 4, 5];
    let values = vec![3, 4, 5, 6];
    let capacity = 8;
    println!("背包问题 - 重量: {:?}, 价值: {:?}, 容量: {}", weights, values, capacity);
    
    let start = Instant::now();
    let max_value = knapsack_01_sync(&weights, &values, capacity);
    println!("同步背包最大价值: {} (耗时: {:?})", max_value, start.elapsed());
    
    let start = Instant::now();
    let max_value = knapsack_01_async(weights, values, capacity).await?;
    println!("异步背包最大价值: {} (耗时: {:?})", max_value, start.elapsed());
    
    // 最长上升子序列
    let sequence = vec![10, 9, 2, 5, 3, 7, 101, 18];
    println!("序列: {:?}", sequence);
    
    let start = Instant::now();
    let lis_len = lis_length_sync(&sequence);
    println!("同步LIS长度: {} (耗时: {:?})", lis_len, start.elapsed());
    
    Ok(())
}

/// 演示分治算法
async fn demo_divide_and_conquer_algorithms() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 分治算法演示 ===");
    
    // 最大子段和
    let array = vec![-2, 1, -3, 4, -1, 2, 1, -5, 4];
    println!("数组: {:?}", array);
    
    let start = Instant::now();
    let max_sum = max_subarray_sum_sync(&array);
    println!("同步最大子段和: {} (耗时: {:?})", max_sum, start.elapsed());
    
    let start = Instant::now();
    let max_sum = max_subarray_sum_async(array).await?;
    println!("异步最大子段和: {} (耗时: {:?})", max_sum, start.elapsed());
    
    // 最近点对
    use c08_algorithms::divide_and_conquer::Point;
    let points = vec![
        Point { x: 0.0, y: 0.0 },
        Point { x: 1.0, y: 1.0 },
        Point { x: 2.0, y: 2.0 },
        Point { x: 3.0, y: 3.0 },
    ];
    println!("点集: {:?}", points);
    
    let start = Instant::now();
    let min_dist = closest_pair_sync(points.clone());
    println!("同步最近点对距离: {} (耗时: {:?})", min_dist, start.elapsed());
    
    let start = Instant::now();
    let min_dist = closest_pair_async(points).await?;
    println!("异步最近点对距离: {} (耗时: {:?})", min_dist, start.elapsed());
    
    // 快速幂
    let base = 2u64;
    let exp = 10u64;
    let modulus = 1000000007u64;
    println!("计算 {}^{} mod {}", base, exp, modulus);
    
    let start = Instant::now();
    let result = fast_pow_mod(base, exp, modulus);
    println!("快速幂结果: {} (耗时: {:?})", result, start.elapsed());
    
    Ok(())
}

/// 演示字符串算法
async fn demo_string_algorithms() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 字符串算法演示 ===");
    
    let text = "ababcabcabababd";
    let pattern = "ababd";
    println!("文本: {}", text);
    println!("模式: {}", pattern);
    
    // KMP搜索
    let start = Instant::now();
    let positions = kmp_search(text, pattern);
    println!("同步KMP搜索结果: {:?} (耗时: {:?})", positions, start.elapsed());
    
    let start = Instant::now();
    let positions = kmp_search_async(text.to_string(), pattern.to_string()).await?;
    println!("异步KMP搜索结果: {:?} (耗时: {:?})", positions, start.elapsed());
    
    // Rabin-Karp搜索
    let text = "abracadabra";
    let pattern = "abra";
    println!("文本: {}", text);
    println!("模式: {}", pattern);
    
    let start = Instant::now();
    let positions = rabin_karp_search(text, pattern);
    println!("同步Rabin-Karp搜索结果: {:?} (耗时: {:?})", positions, start.elapsed());
    
    let start = Instant::now();
    let positions = rabin_karp_search_async(text.to_string(), pattern.to_string()).await?;
    println!("异步Rabin-Karp搜索结果: {:?} (耗时: {:?})", positions, start.elapsed());
    
    // Manacher最长回文
    let text = "babad";
    println!("文本: {}", text);
    
    let start = Instant::now();
    let (start_pos, length) = manacher_longest_palindrome(text);
    println!("同步Manacher最长回文: 起始位置={}, 长度={} (耗时: {:?})", start_pos, length, start.elapsed());
    
    Ok(())
}

/// 演示回溯算法
async fn demo_backtracking_algorithms() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 回溯算法演示 ===");
    
    // N皇后问题
    let n = 4;
    println!("{}皇后问题", n);
    
    let start = Instant::now();
    let solutions = nqueens_solutions_sync(n);
    println!("同步N皇后解数量: {} (耗时: {:?})", solutions.len(), start.elapsed());
    
    let start = Instant::now();
    let solutions = nqueens_solutions_async(n).await?;
    println!("异步N皇后解数量: {} (耗时: {:?})", solutions.len(), start.elapsed());
    
    // 全排列
    let nums = vec![1, 2, 3];
    println!("数组: {:?}", nums);
    
    let start = Instant::now();
    let permutations = permutations_sync(nums.clone());
    println!("同步全排列: {:?} (耗时: {:?})", permutations, start.elapsed());
    
    let start = Instant::now();
    let permutations = permutations_async(nums.clone()).await?;
    println!("异步全排列: {:?} (耗时: {:?})", permutations, start.elapsed());
    
    // 子集生成
    let start = Instant::now();
    let subsets = subsets_sync(&nums);
    println!("同步子集: {:?} (耗时: {:?})", subsets, start.elapsed());
    
    let start = Instant::now();
    let subsets = subsets_async(nums).await?;
    println!("异步子集: {:?} (耗时: {:?})", subsets, start.elapsed());
    
    Ok(())
}

/// 演示贪心算法
async fn demo_greedy_algorithms() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 贪心算法演示 ===");
    
    // 区间调度
    use c08_algorithms::greedy::Interval;
    let intervals = vec![
        Interval { start: 1, end: 3 },
        Interval { start: 2, end: 4 },
        Interval { start: 3, end: 5 },
        Interval { start: 0, end: 7 },
        Interval { start: 5, end: 9 },
    ];
    println!("区间: {:?}", intervals);
    
    let start = Instant::now();
    let selected = interval_scheduling_sync(intervals.clone());
    println!("同步区间调度: {:?} (耗时: {:?})", selected, start.elapsed());
    
    let start = Instant::now();
    let selected = interval_scheduling_async(intervals).await?;
    println!("异步区间调度: {:?} (耗时: {:?})", selected, start.elapsed());
    
    // 零钱兑换
    let coins = vec![1, 5, 10, 25];
    let amount = 41;
    println!("硬币: {:?}, 金额: {}", coins, amount);
    
    let start = Instant::now();
    let result = coin_change_greedy_sync(coins.clone(), amount);
    println!("同步零钱兑换: {:?} (耗时: {:?})", result, start.elapsed());
    
    let start = Instant::now();
    let result = coin_change_greedy_async(coins, amount).await?;
    println!("异步零钱兑换: {:?} (耗时: {:?})", result, start.elapsed());
    
    // 分数背包
    use c08_algorithms::greedy::Item;
    let items = vec![
        Item { weight: 10.0, value: 60.0 },
        Item { weight: 20.0, value: 100.0 },
        Item { weight: 30.0, value: 120.0 },
    ];
    let capacity = 50.0;
    println!("物品: {:?}, 容量: {}", items, capacity);
    
    let start = Instant::now();
    let max_value = fractional_knapsack_sync(items, capacity);
    println!("同步分数背包最大价值: {} (耗时: {:?})", max_value, start.elapsed());
    
    Ok(())
}

/// 性能对比演示
async fn demo_performance_comparison() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 性能对比演示 ===");
    
    // 生成大数据集（使用随机数据以避免快速排序退化）
    use rand::Rng;
    let mut rng = rand::rng();
    let large_data: Vec<i32> = (0..1000).map(|_| rng.random_range(0..1000)).collect();
    println!("大数据集大小: {}", large_data.len());
    
    // 同步排序
    let mut data = large_data.clone();
    let start = Instant::now();
    sort_sync(&mut data, SortingAlgo::Quick);
    let sync_time = start.elapsed();
    println!("同步快速排序耗时: {:?}", sync_time);
    
    // 并行排序
    let mut data = large_data.clone();
    let start = Instant::now();
    sort_parallel(&mut data, SortingAlgo::Quick);
    let parallel_time = start.elapsed();
    println!("并行快速排序耗时: {:?}", parallel_time);
    
    // 异步排序
    let data = large_data.clone();
    let start = Instant::now();
    let _sorted = sort_async(data, SortingAlgo::Quick).await?;
    let async_time = start.elapsed();
    println!("异步快速排序耗时: {:?}", async_time);
    
    // 性能提升分析
    let parallel_speedup = sync_time.as_nanos() as f64 / parallel_time.as_nanos() as f64;
    let async_overhead = async_time.as_nanos() as f64 / sync_time.as_nanos() as f64;
    
    println!("并行加速比: {:.2}x", parallel_speedup);
    println!("异步开销: {:.2}x", async_overhead);
    
    Ok(())
}

/// 主函数
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 Rust 1.89 算法与数据结构综合演示");
    println!("=====================================");
    
    // 运行各种算法演示
    demo_sorting_algorithms().await?;
    demo_searching_algorithms().await?;
    demo_graph_algorithms().await?;
    demo_dynamic_programming_algorithms().await?;
    demo_divide_and_conquer_algorithms().await?;
    demo_string_algorithms().await?;
    demo_backtracking_algorithms().await?;
    demo_greedy_algorithms().await?;
    demo_performance_comparison().await?;
    
    println!("\n✅ 所有算法演示完成！");
    println!("\n📚 更多信息请查看:");
    println!("- 算法索引: docs/ALGORITHM_INDEX_RUST_189.md");
    println!("- Rust 1.89 特性指南: docs/RUST_189_FEATURES_GUIDE.md");
    println!("- 性能基准测试: cargo bench");
    
    Ok(())
}
