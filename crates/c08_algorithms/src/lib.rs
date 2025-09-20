//! Rust高级算法实现库
//!
//! 本库提供了Rust中各种高级算法的完整实现，
//! 包括排序、搜索、图算法、机器学习算法、密码学算法等。

// 基础算法模块
pub mod backtracking;
pub mod data_structure;
pub mod divide_and_conquer;
pub mod dynamic_programming;
pub mod graph;
pub mod greedy;
pub mod searching;
pub mod sorting;

// 高级算法模块
pub mod advanced_algorithms;

// 机器学习模块
pub mod machine_learning;

// 性能优化模块
pub mod geometry;
pub mod number_theory;
pub mod performance_examples;
pub mod performance_optimization;
pub mod string_algorithms;

// 示例程序
// pub mod bin; // 暂时注释掉，避免编译错误

/// 算法库版本信息
pub const VERSION: &str = "0.1.0";

/// 获取库版本信息
pub fn get_version() -> &'static str {
    VERSION
}

/// 算法分类
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AlgorithmCategory {
    Sorting,
    Searching,
    Graph,
    DynamicProgramming,
    DivideAndConquer,
    Greedy,
    Backtracking,
    MachineLearning,
    Cryptography,
    PerformanceOptimization,
}

/// 算法信息
#[derive(Debug, Clone)]
pub struct AlgorithmInfo {
    pub name: String,
    pub category: AlgorithmCategory,
    pub description: String,
    pub time_complexity: String,
    pub space_complexity: String,
    pub use_cases: Vec<String>,
}

/// 获取所有算法信息
pub fn get_all_algorithms() -> Vec<AlgorithmInfo> {
    vec![
        // 排序算法
        AlgorithmInfo {
            name: "快速排序".to_string(),
            category: AlgorithmCategory::Sorting,
            description: "基于分治策略的高效排序算法".to_string(),
            time_complexity: "O(n log n)".to_string(),
            space_complexity: "O(log n)".to_string(),
            use_cases: vec![
                "大规模数据排序".to_string(),
                "系统排序实现".to_string(),
                "实时排序应用".to_string(),
            ],
        },
        AlgorithmInfo {
            name: "归并排序".to_string(),
            category: AlgorithmCategory::Sorting,
            description: "稳定的分治排序算法".to_string(),
            time_complexity: "O(n log n)".to_string(),
            space_complexity: "O(n)".to_string(),
            use_cases: vec![
                "外部排序".to_string(),
                "链表排序".to_string(),
                "稳定排序需求".to_string(),
            ],
        },
        AlgorithmInfo {
            name: "堆排序".to_string(),
            category: AlgorithmCategory::Sorting,
            description: "基于堆数据结构的排序算法".to_string(),
            time_complexity: "O(n log n)".to_string(),
            space_complexity: "O(1)".to_string(),
            use_cases: vec![
                "原地排序".to_string(),
                "优先队列实现".to_string(),
                "内存受限环境".to_string(),
            ],
        },
        // 搜索算法
        AlgorithmInfo {
            name: "二分搜索".to_string(),
            category: AlgorithmCategory::Searching,
            description: "在有序数组中查找元素的算法".to_string(),
            time_complexity: "O(log n)".to_string(),
            space_complexity: "O(1)".to_string(),
            use_cases: vec![
                "有序数组查找".to_string(),
                "数值计算".to_string(),
                "游戏AI".to_string(),
            ],
        },
        AlgorithmInfo {
            name: "深度优先搜索".to_string(),
            category: AlgorithmCategory::Searching,
            description: "图遍历算法，优先探索深层节点".to_string(),
            time_complexity: "O(V + E)".to_string(),
            space_complexity: "O(V)".to_string(),
            use_cases: vec![
                "图遍历".to_string(),
                "迷宫求解".to_string(),
                "拓扑排序".to_string(),
            ],
        },
        AlgorithmInfo {
            name: "广度优先搜索".to_string(),
            category: AlgorithmCategory::Searching,
            description: "图遍历算法，优先探索近邻节点".to_string(),
            time_complexity: "O(V + E)".to_string(),
            space_complexity: "O(V)".to_string(),
            use_cases: vec![
                "最短路径".to_string(),
                "网络爬虫".to_string(),
                "社交网络分析".to_string(),
            ],
        },
        // 图算法
        AlgorithmInfo {
            name: "Dijkstra算法".to_string(),
            category: AlgorithmCategory::Graph,
            description: "单源最短路径算法".to_string(),
            time_complexity: "O((V + E) log V)".to_string(),
            space_complexity: "O(V)".to_string(),
            use_cases: vec![
                "路由算法".to_string(),
                "网络优化".to_string(),
                "游戏AI路径规划".to_string(),
            ],
        },
        AlgorithmInfo {
            name: "Kruskal算法".to_string(),
            category: AlgorithmCategory::Graph,
            description: "最小生成树算法".to_string(),
            time_complexity: "O(E log E)".to_string(),
            space_complexity: "O(V)".to_string(),
            use_cases: vec![
                "网络设计".to_string(),
                "聚类分析".to_string(),
                "电路设计".to_string(),
            ],
        },
        // 动态规划
        AlgorithmInfo {
            name: "最长公共子序列".to_string(),
            category: AlgorithmCategory::DynamicProgramming,
            description: "求解两个序列的最长公共子序列".to_string(),
            time_complexity: "O(mn)".to_string(),
            space_complexity: "O(mn)".to_string(),
            use_cases: vec![
                "DNA序列比对".to_string(),
                "文本相似度".to_string(),
                "版本控制".to_string(),
            ],
        },
        AlgorithmInfo {
            name: "背包问题".to_string(),
            category: AlgorithmCategory::DynamicProgramming,
            description: "经典的0-1背包问题求解".to_string(),
            time_complexity: "O(nW)".to_string(),
            space_complexity: "O(nW)".to_string(),
            use_cases: vec![
                "资源分配".to_string(),
                "投资组合".to_string(),
                "装载问题".to_string(),
            ],
        },
        // 机器学习算法
        AlgorithmInfo {
            name: "线性回归".to_string(),
            category: AlgorithmCategory::MachineLearning,
            description: "基础的线性回归算法".to_string(),
            time_complexity: "O(n)".to_string(),
            space_complexity: "O(1)".to_string(),
            use_cases: vec![
                "预测分析".to_string(),
                "趋势分析".to_string(),
                "数据建模".to_string(),
            ],
        },
        AlgorithmInfo {
            name: "K-means聚类".to_string(),
            category: AlgorithmCategory::MachineLearning,
            description: "经典的聚类算法".to_string(),
            time_complexity: "O(nkd)".to_string(),
            space_complexity: "O(n)".to_string(),
            use_cases: vec![
                "客户分群".to_string(),
                "图像分割".to_string(),
                "数据挖掘".to_string(),
            ],
        },
        // 密码学算法
        AlgorithmInfo {
            name: "RSA加密".to_string(),
            category: AlgorithmCategory::Cryptography,
            description: "非对称加密算法".to_string(),
            time_complexity: "O(n³)".to_string(),
            space_complexity: "O(n)".to_string(),
            use_cases: vec![
                "数字签名".to_string(),
                "密钥交换".to_string(),
                "安全通信".to_string(),
            ],
        },
        AlgorithmInfo {
            name: "SHA-256哈希".to_string(),
            category: AlgorithmCategory::Cryptography,
            description: "安全哈希算法".to_string(),
            time_complexity: "O(n)".to_string(),
            space_complexity: "O(1)".to_string(),
            use_cases: vec![
                "数据完整性".to_string(),
                "密码存储".to_string(),
                "区块链".to_string(),
            ],
        },
        // 性能优化
        AlgorithmInfo {
            name: "内存池".to_string(),
            category: AlgorithmCategory::PerformanceOptimization,
            description: "内存分配优化技术".to_string(),
            time_complexity: "O(1)".to_string(),
            space_complexity: "O(n)".to_string(),
            use_cases: vec![
                "高频分配".to_string(),
                "游戏引擎".to_string(),
                "实时系统".to_string(),
            ],
        },
        AlgorithmInfo {
            name: "无锁数据结构".to_string(),
            category: AlgorithmCategory::PerformanceOptimization,
            description: "并发性能优化技术".to_string(),
            time_complexity: "O(1)".to_string(),
            space_complexity: "O(1)".to_string(),
            use_cases: vec![
                "高并发系统".to_string(),
                "实时计算".to_string(),
                "多核优化".to_string(),
            ],
        },
    ]
}

/// 根据分类获取算法
pub fn get_algorithms_by_category(category: AlgorithmCategory) -> Vec<AlgorithmInfo> {
    get_all_algorithms()
        .into_iter()
        .filter(|algorithm| algorithm.category == category)
        .collect()
}

/// 搜索算法
pub fn search_algorithms(query: &str) -> Vec<AlgorithmInfo> {
    let query_lower = query.to_lowercase();
    get_all_algorithms()
        .into_iter()
        .filter(|algorithm| {
            algorithm.name.to_lowercase().contains(&query_lower)
                || algorithm.description.to_lowercase().contains(&query_lower)
                || algorithm.use_cases.iter().any(|case| case.to_lowercase().contains(&query_lower))
                // 额外匹配：按分类的常见中文/英文关键词
                || match algorithm.category {
                    AlgorithmCategory::Sorting => ["排序", "sort", "quick", "merge", "radix"].iter().any(|k| query_lower.contains(k)),
                    AlgorithmCategory::Searching => ["搜索", "search", "二分", "binary"].iter().any(|k| query_lower.contains(k)),
                    AlgorithmCategory::Graph => ["图", "graph", "最短", "shortest"].iter().any(|k| query_lower.contains(k)),
                    AlgorithmCategory::DynamicProgramming => ["动态规划", "dp", "dynamic"].iter().any(|k| query_lower.contains(k)),
                    AlgorithmCategory::Greedy => ["贪心", "greedy"].iter().any(|k| query_lower.contains(k)),
                    AlgorithmCategory::DivideAndConquer => ["分治", "divide", "conquer"].iter().any(|k| query_lower.contains(k)),
                    AlgorithmCategory::Backtracking => ["回溯", "backtrack"].iter().any(|k| query_lower.contains(k)),
                    AlgorithmCategory::MachineLearning => ["机器学习", "learning", "regression", "kmeans"].iter().any(|k| query_lower.contains(k)),
                    AlgorithmCategory::Cryptography => ["密码", "crypto", "rsa", "aes", "sha"].iter().any(|k| query_lower.contains(k)),
                    AlgorithmCategory::PerformanceOptimization => ["性能", "优化", "performance", "pool", "parallel"].iter().any(|k| query_lower.contains(k)),
                }
        })
        .collect()
}

/// 算法性能基准测试
pub struct AlgorithmBenchmark {
    results: std::collections::HashMap<String, Vec<std::time::Duration>>,
}

impl Default for AlgorithmBenchmark {
    fn default() -> Self {
        Self::new()
    }
}

impl AlgorithmBenchmark {
    pub fn new() -> Self {
        Self {
            results: std::collections::HashMap::new(),
        }
    }

    pub fn run_benchmark<F>(&mut self, name: &str, iterations: usize, test_fn: F)
    where
        F: Fn(),
    {
        let start = std::time::Instant::now();

        for _ in 0..iterations {
            test_fn();
        }

        let duration = start.elapsed();
        self.results
            .entry(name.to_string())
            .or_default()
            .push(duration);
    }

    pub fn get_average_time(&self, name: &str) -> Option<std::time::Duration> {
        self.results.get(name).map(|durations| {
            let total: std::time::Duration = durations.iter().sum();
            total / durations.len() as u32
        })
    }

    pub fn generate_report(&self) -> String {
        let mut report = String::from("算法性能基准测试报告\n");
        report.push_str("========================\n\n");

        for (name, durations) in &self.results {
            let avg = durations.iter().sum::<std::time::Duration>() / durations.len() as u32;
            let min = durations.iter().min().unwrap();
            let max = durations.iter().max().unwrap();

            report.push_str(&format!("{}:\n", name));
            report.push_str(&format!("  平均时间: {:?}\n", avg));
            report.push_str(&format!("  最短时间: {:?}\n", min));
            report.push_str(&format!("  最长时间: {:?}\n", max));
            report.push_str(&format!("  测试次数: {}\n\n", durations.len()));
        }

        report
    }
}

/// 算法复杂度分析器
pub struct ComplexityAnalyzer;

impl ComplexityAnalyzer {
    /// 分析算法的时间复杂度
    pub fn analyze_time_complexity<F>(
        test_fn: F,
        input_sizes: &[usize],
    ) -> Vec<(usize, std::time::Duration)>
    where
        F: Fn(usize),
    {
        let mut results = Vec::new();

        for &size in input_sizes {
            let start = std::time::Instant::now();
            test_fn(size);
            let duration = start.elapsed();
            results.push((size, duration));
        }

        results
    }

    /// 估算算法的时间复杂度
    pub fn estimate_complexity(results: &[(usize, std::time::Duration)]) -> String {
        if results.len() < 2 {
            return "数据不足".to_string();
        }

        let (size1, time1) = results[0];
        let (size2, time2) = results[results.len() - 1];

        let ratio = size2 as f64 / size1 as f64;
        let time_ratio = time2.as_nanos() as f64 / time1.as_nanos() as f64;

        let log_ratio = ratio.ln();
        let log_time_ratio = time_ratio.ln();

        let complexity = if log_time_ratio < 1.5 {
            "O(1)"
        } else if log_time_ratio < log_ratio * 1.2 {
            "O(log n)"
        } else if log_time_ratio < log_ratio * 1.5 {
            "O(n)"
        } else if log_time_ratio < log_ratio * 2.2 {
            "O(n log n)"
        } else if log_time_ratio < log_ratio * 2.5 {
            "O(n²)"
        } else {
            "O(n³) 或更高"
        };

        complexity.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_all_algorithms() {
        let algorithms = get_all_algorithms();
        assert!(!algorithms.is_empty());

        // 检查是否包含所有分类
        let categories: std::collections::HashSet<_> =
            algorithms.iter().map(|a| &a.category).collect();

        assert!(categories.contains(&AlgorithmCategory::Sorting));
        assert!(categories.contains(&AlgorithmCategory::Searching));
        assert!(categories.contains(&AlgorithmCategory::Graph));
        assert!(categories.contains(&AlgorithmCategory::DynamicProgramming));
        assert!(categories.contains(&AlgorithmCategory::MachineLearning));
        assert!(categories.contains(&AlgorithmCategory::Cryptography));
        assert!(categories.contains(&AlgorithmCategory::PerformanceOptimization));
    }

    #[test]
    fn test_get_algorithms_by_category() {
        let sorting_algorithms = get_algorithms_by_category(AlgorithmCategory::Sorting);
        assert!(!sorting_algorithms.is_empty());

        for algorithm in sorting_algorithms {
            assert_eq!(algorithm.category, AlgorithmCategory::Sorting);
        }
    }

    #[test]
    fn test_search_algorithms() {
        let results = search_algorithms("排序");
        assert!(!results.is_empty());

        let results = search_algorithms("quick");
        assert!(!results.is_empty());

        let results = search_algorithms("nonexistent");
        assert!(results.is_empty());
    }

    #[test]
    fn test_algorithm_benchmark() {
        let mut benchmark = AlgorithmBenchmark::new();

        benchmark.run_benchmark("测试算法", 100, || {
            // 模拟算法执行
            std::thread::sleep(std::time::Duration::from_micros(100));
        });

        let avg_time = benchmark.get_average_time("测试算法");
        assert!(avg_time.is_some());
        assert!(avg_time.unwrap() >= std::time::Duration::from_micros(100));
    }

    #[test]
    fn test_complexity_analyzer() {
        let input_sizes = vec![100, 1000, 10000];
        let results = ComplexityAnalyzer::analyze_time_complexity(
            |size| {
                // 模拟O(n)算法
                for _ in 0..size {
                    std::thread::sleep(std::time::Duration::from_nanos(1));
                }
            },
            &input_sizes,
        );

        assert_eq!(results.len(), 3);

        let complexity = ComplexityAnalyzer::estimate_complexity(&results);
        assert!(!complexity.is_empty());
    }

    #[test]
    fn test_version() {
        assert_eq!(get_version(), "0.1.0");
    }
}
