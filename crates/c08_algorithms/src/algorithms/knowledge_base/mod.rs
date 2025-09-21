//! # 算法知识体系模块
//! 
//! 本模块整合了完整的算法知识体系，包括理论基础、应用场景、最佳实践等。
//! 为算法学习和应用提供全面的知识支持。

pub mod theory;
pub mod applications;
pub mod best_practices;

// 重新导出知识体系相关类型
pub use theory::*;
pub use applications::*;
pub use best_practices::*;

use std::collections::HashMap;
use serde::{Serialize, Deserialize};

/// 算法知识库
pub struct AlgorithmKnowledgeBase {
    algorithms: HashMap<String, AlgorithmKnowledge>,
    categories: HashMap<String, CategoryKnowledge>,
    applications: HashMap<String, ApplicationKnowledge>,
}

/// 算法知识
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlgorithmKnowledge {
    pub name: String,
    pub category: String,
    pub description: String,
    pub theory: TheoryKnowledge,
    pub implementation: ImplementationKnowledge,
    pub applications: Vec<String>,
    pub related_algorithms: Vec<String>,
    pub complexity: ComplexityKnowledge,
    pub variants: Vec<AlgorithmVariant>,
    pub history: HistoryKnowledge,
}

/// 理论知识
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TheoryKnowledge {
    pub mathematical_foundation: String,
    pub key_concepts: Vec<String>,
    pub invariants: Vec<String>,
    pub proof_techniques: Vec<String>,
    pub formal_specification: Option<String>,
}

/// 实现知识
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImplementationKnowledge {
    pub pseudocode: String,
    pub rust_implementation: String,
    pub optimization_techniques: Vec<String>,
    pub common_pitfalls: Vec<String>,
    pub testing_strategies: Vec<String>,
}

/// 复杂度知识
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplexityKnowledge {
    pub time_complexity: ComplexityBounds,
    pub space_complexity: ComplexityBounds,
    pub best_case_analysis: String,
    pub average_case_analysis: String,
    pub worst_case_analysis: String,
    pub amortized_analysis: Option<String>,
    pub practical_performance: String,
}

/// 复杂度边界
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplexityBounds {
    pub lower_bound: String,
    pub upper_bound: String,
    pub tight_bound: Option<String>,
    pub proof: Option<String>,
}

/// 算法变体
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlgorithmVariant {
    pub name: String,
    pub description: String,
    pub modifications: Vec<String>,
    pub use_cases: Vec<String>,
    pub complexity_changes: Option<ComplexityKnowledge>,
}

/// 历史知识
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistoryKnowledge {
    pub inventor: Option<String>,
    pub year: Option<u32>,
    pub development_history: Vec<String>,
    pub milestones: Vec<String>,
    pub current_research: Vec<String>,
}

/// 分类知识
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CategoryKnowledge {
    pub name: String,
    pub description: String,
    pub key_algorithms: Vec<String>,
    pub common_patterns: Vec<String>,
    pub design_principles: Vec<String>,
    pub applications: Vec<String>,
    pub learning_path: Vec<String>,
}

/// 应用知识
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApplicationKnowledge {
    pub domain: String,
    pub description: String,
    pub algorithms_used: Vec<String>,
    pub performance_requirements: Vec<String>,
    pub implementation_considerations: Vec<String>,
    pub real_world_examples: Vec<String>,
}

impl AlgorithmKnowledgeBase {
    /// 创建新的算法知识库
    pub fn new() -> Self {
        let mut knowledge_base = Self {
            algorithms: HashMap::new(),
            categories: HashMap::new(),
            applications: HashMap::new(),
        };
        
        knowledge_base.initialize_knowledge();
        knowledge_base
    }

    /// 初始化知识库
    fn initialize_knowledge(&mut self) {
        self.initialize_sorting_algorithms();
        self.initialize_searching_algorithms();
        self.initialize_graph_algorithms();
        self.initialize_dynamic_programming_algorithms();
        self.initialize_categories();
        self.initialize_applications();
    }

    /// 初始化排序算法知识
    fn initialize_sorting_algorithms(&mut self) {
        // 快速排序
        self.algorithms.insert("QuickSort".to_string(), AlgorithmKnowledge {
            name: "快速排序".to_string(),
            category: "排序".to_string(),
            description: "基于分治策略的高效排序算法，通过选择基准元素将数组分为两部分".to_string(),
            theory: TheoryKnowledge {
                mathematical_foundation: "分治算法，基于比较的排序".to_string(),
                key_concepts: vec![
                    "分治策略".to_string(),
                    "基准选择".to_string(),
                    "分区操作".to_string(),
                    "递归排序".to_string(),
                ],
                invariants: vec![
                    "分区后基准元素左侧都小于等于基准".to_string(),
                    "分区后基准元素右侧都大于基准".to_string(),
                ],
                proof_techniques: vec![
                    "循环不变式".to_string(),
                    "数学归纳法".to_string(),
                    "分治分析".to_string(),
                ],
                formal_specification: Some("Hoare 逻辑".to_string()),
            },
            implementation: ImplementationKnowledge {
                pseudocode: r#"
function quicksort(array, low, high):
    if low < high:
        pivot = partition(array, low, high)
        quicksort(array, low, pivot - 1)
        quicksort(array, pivot + 1, high)

function partition(array, low, high):
    pivot = array[high]
    i = low
    for j = low to high - 1:
        if array[j] <= pivot:
            swap array[i] and array[j]
            i = i + 1
    swap array[i] and array[high]
    return i
                "#.to_string(),
                rust_implementation: "见 src/algorithms/sorting/sync.rs".to_string(),
                optimization_techniques: vec![
                    "三数取中法选择基准".to_string(),
                    "小数组使用插入排序".to_string(),
                    "尾递归优化".to_string(),
                    "三路快排处理重复元素".to_string(),
                ],
                common_pitfalls: vec![
                    "基准选择不当导致最坏情况".to_string(),
                    "递归深度过深导致栈溢出".to_string(),
                    "分区操作实现错误".to_string(),
                ],
                testing_strategies: vec![
                    "随机数据测试".to_string(),
                    "已排序数据测试".to_string(),
                    "逆序数据测试".to_string(),
                    "重复元素测试".to_string(),
                ],
            },
            applications: vec![
                "通用排序".to_string(),
                "数据库查询优化".to_string(),
                "操作系统调度".to_string(),
                "编译器优化".to_string(),
            ],
            related_algorithms: vec![
                "归并排序".to_string(),
                "堆排序".to_string(),
                "内省排序".to_string(),
            ],
            complexity: ComplexityKnowledge {
                time_complexity: ComplexityBounds {
                    lower_bound: "Ω(n log n)".to_string(),
                    upper_bound: "O(n²)".to_string(),
                    tight_bound: Some("Θ(n log n) 平均情况".to_string()),
                    proof: Some("分治分析".to_string()),
                },
                space_complexity: ComplexityBounds {
                    lower_bound: "Ω(log n)".to_string(),
                    upper_bound: "O(log n)".to_string(),
                    tight_bound: Some("Θ(log n)".to_string()),
                    proof: Some("递归深度分析".to_string()),
                },
                best_case_analysis: "每次分区都平衡，递归深度为 log n".to_string(),
                average_case_analysis: "随机化基准选择，期望性能 O(n log n)".to_string(),
                worst_case_analysis: "每次分区都不平衡，递归深度为 n".to_string(),
                amortized_analysis: Some("平均情况下 O(n log n)".to_string()),
                practical_performance: "实际应用中表现优异，常数因子小".to_string(),
            },
            variants: vec![
                AlgorithmVariant {
                    name: "三路快排".to_string(),
                    description: "处理重复元素的优化版本".to_string(),
                    modifications: vec!["三路分区".to_string()],
                    use_cases: vec!["大量重复元素".to_string()],
                    complexity_changes: None,
                },
                AlgorithmVariant {
                    name: "内省排序".to_string(),
                    description: "结合快排和堆排序的混合算法".to_string(),
                    modifications: vec!["递归深度限制".to_string(), "堆排序回退".to_string()],
                    use_cases: vec!["保证 O(n log n) 性能".to_string()],
                    complexity_changes: Some(ComplexityKnowledge {
                        time_complexity: ComplexityBounds {
                            lower_bound: "Ω(n log n)".to_string(),
                            upper_bound: "O(n log n)".to_string(),
                            tight_bound: Some("Θ(n log n)".to_string()),
                            proof: Some("混合分析".to_string()),
                        },
                        space_complexity: ComplexityBounds {
                            lower_bound: "Ω(log n)".to_string(),
                            upper_bound: "O(log n)".to_string(),
                            tight_bound: Some("Θ(log n)".to_string()),
                            proof: Some("递归深度限制".to_string()),
                        },
                        best_case_analysis: "快排性能".to_string(),
                        average_case_analysis: "快排性能".to_string(),
                        worst_case_analysis: "堆排序性能".to_string(),
                        amortized_analysis: Some("O(n log n)".to_string()),
                        practical_performance: "保证最坏情况性能".to_string(),
                    }),
                },
            ],
            history: HistoryKnowledge {
                inventor: Some("Tony Hoare".to_string()),
                year: Some(1960),
                development_history: vec![
                    "1960年由 Tony Hoare 发明".to_string(),
                    "1970年代广泛采用".to_string(),
                    "1980年代优化技术发展".to_string(),
                    "1990年代三路快排出现".to_string(),
                ],
                milestones: vec![
                    "原始算法".to_string(),
                    "随机化版本".to_string(),
                    "三路快排".to_string(),
                    "内省排序".to_string(),
                ],
                current_research: vec![
                    "并行化研究".to_string(),
                    "缓存优化".to_string(),
                    "SIMD 优化".to_string(),
                ],
            },
        });

        // 归并排序
        self.algorithms.insert("MergeSort".to_string(), AlgorithmKnowledge {
            name: "归并排序".to_string(),
            category: "排序".to_string(),
            description: "稳定的分治排序算法，通过递归分治和合并操作实现排序".to_string(),
            theory: TheoryKnowledge {
                mathematical_foundation: "分治算法，基于比较的稳定排序".to_string(),
                key_concepts: vec![
                    "分治策略".to_string(),
                    "合并操作".to_string(),
                    "稳定性".to_string(),
                ],
                invariants: vec![
                    "合并后的数组保持有序".to_string(),
                    "相等元素的相对位置不变".to_string(),
                ],
                proof_techniques: vec![
                    "数学归纳法".to_string(),
                    "分治分析".to_string(),
                ],
                formal_specification: Some("递归规范".to_string()),
            },
            implementation: ImplementationKnowledge {
                pseudocode: r#"
function mergesort(array):
    if length(array) <= 1:
        return array
    mid = length(array) / 2
    left = mergesort(array[0:mid])
    right = mergesort(array[mid:])
    return merge(left, right)

function merge(left, right):
    result = []
    i = j = 0
    while i < length(left) and j < length(right):
        if left[i] <= right[j]:
            result.append(left[i])
            i = i + 1
        else:
            result.append(right[j])
            j = j + 1
    result.extend(left[i:])
    result.extend(right[j:])
    return result
                "#.to_string(),
                rust_implementation: "见 src/algorithms/sorting/sync.rs".to_string(),
                optimization_techniques: vec![
                    "原地合并".to_string(),
                    "小数组使用插入排序".to_string(),
                    "避免重复分配".to_string(),
                ],
                common_pitfalls: vec![
                    "合并操作实现错误".to_string(),
                    "内存使用过多".to_string(),
                ],
                testing_strategies: vec![
                    "稳定性测试".to_string(),
                    "边界情况测试".to_string(),
                ],
            },
            applications: vec![
                "稳定排序需求".to_string(),
                "外部排序".to_string(),
                "链表排序".to_string(),
            ],
            related_algorithms: vec![
                "快速排序".to_string(),
                "堆排序".to_string(),
                "外部归并排序".to_string(),
            ],
            complexity: ComplexityKnowledge {
                time_complexity: ComplexityBounds {
                    lower_bound: "Ω(n log n)".to_string(),
                    upper_bound: "O(n log n)".to_string(),
                    tight_bound: Some("Θ(n log n)".to_string()),
                    proof: Some("分治分析".to_string()),
                },
                space_complexity: ComplexityBounds {
                    lower_bound: "Ω(n)".to_string(),
                    upper_bound: "O(n)".to_string(),
                    tight_bound: Some("Θ(n)".to_string()),
                    proof: Some("合并操作需要额外空间".to_string()),
                },
                best_case_analysis: "O(n log n)".to_string(),
                average_case_analysis: "O(n log n)".to_string(),
                worst_case_analysis: "O(n log n)".to_string(),
                amortized_analysis: None,
                practical_performance: "性能稳定，但空间开销较大".to_string(),
            },
            variants: vec![],
            history: HistoryKnowledge {
                inventor: Some("John von Neumann".to_string()),
                year: Some(1945),
                development_history: vec![
                    "1945年由 John von Neumann 发明".to_string(),
                    "早期计算机时代的重要算法".to_string(),
                ],
                milestones: vec![
                    "原始算法".to_string(),
                    "原地合并优化".to_string(),
                ],
                current_research: vec![
                    "并行化研究".to_string(),
                    "外部排序优化".to_string(),
                ],
            },
        });
    }

    /// 初始化搜索算法知识
    fn initialize_searching_algorithms(&mut self) {
        // 二分搜索
        self.algorithms.insert("BinarySearch".to_string(), AlgorithmKnowledge {
            name: "二分搜索".to_string(),
            category: "搜索".to_string(),
            description: "在有序数组中查找目标元素的高效搜索算法".to_string(),
            theory: TheoryKnowledge {
                mathematical_foundation: "分治搜索，基于有序性".to_string(),
                key_concepts: vec![
                    "搜索空间缩减".to_string(),
                    "有序性利用".to_string(),
                    "循环不变式".to_string(),
                ],
                invariants: vec![
                    "目标元素（如果存在）在搜索范围内".to_string(),
                ],
                proof_techniques: vec![
                    "循环不变式".to_string(),
                    "数学归纳法".to_string(),
                ],
                formal_specification: Some("Hoare 逻辑".to_string()),
            },
            implementation: ImplementationKnowledge {
                pseudocode: r#"
function binary_search(array, target):
    left = 0
    right = length(array) - 1
    while left <= right:
        mid = (left + right) / 2
        if array[mid] == target:
            return mid
        elif array[mid] < target:
            left = mid + 1
        else:
            right = mid - 1
    return -1
                "#.to_string(),
                rust_implementation: "见 src/algorithms/searching/".to_string(),
                optimization_techniques: vec![
                    "避免整数溢出".to_string(),
                    "分支预测优化".to_string(),
                ],
                common_pitfalls: vec![
                    "边界条件处理错误".to_string(),
                    "整数溢出".to_string(),
                ],
                testing_strategies: vec![
                    "边界值测试".to_string(),
                    "存在性测试".to_string(),
                    "不存在性测试".to_string(),
                ],
            },
            applications: vec![
                "有序数组搜索".to_string(),
                "数据库索引".to_string(),
                "数值计算".to_string(),
            ],
            related_algorithms: vec![
                "线性搜索".to_string(),
                "插值搜索".to_string(),
                "三分搜索".to_string(),
            ],
            complexity: ComplexityKnowledge {
                time_complexity: ComplexityBounds {
                    lower_bound: "Ω(log n)".to_string(),
                    upper_bound: "O(log n)".to_string(),
                    tight_bound: Some("Θ(log n)".to_string()),
                    proof: Some("搜索空间每次减半".to_string()),
                },
                space_complexity: ComplexityBounds {
                    lower_bound: "Ω(1)".to_string(),
                    upper_bound: "O(1)".to_string(),
                    tight_bound: Some("Θ(1)".to_string()),
                    proof: Some("只使用常数空间".to_string()),
                },
                best_case_analysis: "O(1) - 目标在中间".to_string(),
                average_case_analysis: "O(log n)".to_string(),
                worst_case_analysis: "O(log n)".to_string(),
                amortized_analysis: None,
                practical_performance: "非常高效，常数因子小".to_string(),
            },
            variants: vec![],
            history: HistoryKnowledge {
                inventor: None,
                year: Some(1946),
                development_history: vec![
                    "1946年首次描述".to_string(),
                    "计算机科学基础算法".to_string(),
                ],
                milestones: vec![
                    "原始算法".to_string(),
                    "变体算法".to_string(),
                ],
                current_research: vec![
                    "SIMD 优化".to_string(),
                    "缓存优化".to_string(),
                ],
            },
        });
    }

    /// 初始化图算法知识
    fn initialize_graph_algorithms(&mut self) {
        // BFS
        self.algorithms.insert("BFS".to_string(), AlgorithmKnowledge {
            name: "广度优先搜索".to_string(),
            category: "图算法".to_string(),
            description: "从起始节点开始，逐层遍历图的搜索算法".to_string(),
            theory: TheoryKnowledge {
                mathematical_foundation: "图遍历，队列数据结构".to_string(),
                key_concepts: vec![
                    "队列操作".to_string(),
                    "访问标记".to_string(),
                    "层次遍历".to_string(),
                ],
                invariants: vec![
                    "队列中存储待访问节点".to_string(),
                    "已访问节点不再入队".to_string(),
                ],
                proof_techniques: vec![
                    "循环不变式".to_string(),
                    "数学归纳法".to_string(),
                ],
                formal_specification: Some("状态机".to_string()),
            },
            implementation: ImplementationKnowledge {
                pseudocode: r#"
function bfs(graph, start):
    queue = [start]
    visited = {start}
    while queue is not empty:
        node = queue.dequeue()
        for neighbor in graph.neighbors(node):
            if neighbor not in visited:
                visited.add(neighbor)
                queue.enqueue(neighbor)
    return visited
                "#.to_string(),
                rust_implementation: "见 src/algorithms/graph/".to_string(),
                optimization_techniques: vec![
                    "邻接表表示".to_string(),
                    "位图标记".to_string(),
                ],
                common_pitfalls: vec![
                    "重复访问".to_string(),
                    "队列溢出".to_string(),
                ],
                testing_strategies: vec![
                    "连通性测试".to_string(),
                    "最短路径测试".to_string(),
                ],
            },
            applications: vec![
                "最短路径（无权图）".to_string(),
                "连通性检测".to_string(),
                "层次遍历".to_string(),
            ],
            related_algorithms: vec![
                "深度优先搜索".to_string(),
                "Dijkstra 算法".to_string(),
            ],
            complexity: ComplexityKnowledge {
                time_complexity: ComplexityBounds {
                    lower_bound: "Ω(V + E)".to_string(),
                    upper_bound: "O(V + E)".to_string(),
                    tight_bound: Some("Θ(V + E)".to_string()),
                    proof: Some("每个节点和边访问一次".to_string()),
                },
                space_complexity: ComplexityBounds {
                    lower_bound: "Ω(V)".to_string(),
                    upper_bound: "O(V)".to_string(),
                    tight_bound: Some("Θ(V)".to_string()),
                    proof: Some("队列和访问标记".to_string()),
                },
                best_case_analysis: "O(V + E)".to_string(),
                average_case_analysis: "O(V + E)".to_string(),
                worst_case_analysis: "O(V + E)".to_string(),
                amortized_analysis: None,
                practical_performance: "性能稳定，适合无权图".to_string(),
            },
            variants: vec![],
            history: HistoryKnowledge {
                inventor: None,
                year: Some(1950),
                development_history: vec![
                    "1950年代发展".to_string(),
                    "图论基础算法".to_string(),
                ],
                milestones: vec![
                    "原始算法".to_string(),
                    "优化版本".to_string(),
                ],
                current_research: vec![
                    "并行化研究".to_string(),
                    "分布式版本".to_string(),
                ],
            },
        });
    }

    /// 初始化动态规划算法知识
    fn initialize_dynamic_programming_algorithms(&mut self) {
        // 最长公共子序列
        self.algorithms.insert("LCS".to_string(), AlgorithmKnowledge {
            name: "最长公共子序列".to_string(),
            category: "动态规划".to_string(),
            description: "找到两个序列的最长公共子序列的动态规划算法".to_string(),
            theory: TheoryKnowledge {
                mathematical_foundation: "动态规划，最优子结构".to_string(),
                key_concepts: vec![
                    "最优子结构".to_string(),
                    "重叠子问题".to_string(),
                    "状态转移方程".to_string(),
                ],
                invariants: vec![
                    "dp[i][j] 表示前i个和前j个元素的最长公共子序列长度".to_string(),
                ],
                proof_techniques: vec![
                    "数学归纳法".to_string(),
                    "最优子结构证明".to_string(),
                ],
                formal_specification: Some("递归关系".to_string()),
            },
            implementation: ImplementationKnowledge {
                pseudocode: r#"
function lcs(X, Y):
    m = length(X)
    n = length(Y)
    dp = array[m+1][n+1]
    for i = 0 to m:
        for j = 0 to n:
            if i == 0 or j == 0:
                dp[i][j] = 0
            elif X[i-1] == Y[j-1]:
                dp[i][j] = dp[i-1][j-1] + 1
            else:
                dp[i][j] = max(dp[i-1][j], dp[i][j-1])
    return dp[m][n]
                "#.to_string(),
                rust_implementation: "见 src/algorithms/dynamic_programming/".to_string(),
                optimization_techniques: vec![
                    "空间优化".to_string(),
                    "滚动数组".to_string(),
                ],
                common_pitfalls: vec![
                    "边界条件处理".to_string(),
                    "状态转移错误".to_string(),
                ],
                testing_strategies: vec![
                    "边界测试".to_string(),
                    "相同序列测试".to_string(),
                ],
            },
            applications: vec![
                "生物信息学".to_string(),
                "版本控制".to_string(),
                "文本比较".to_string(),
            ],
            related_algorithms: vec![
                "最长公共子串".to_string(),
                "编辑距离".to_string(),
            ],
            complexity: ComplexityKnowledge {
                time_complexity: ComplexityBounds {
                    lower_bound: "Ω(mn)".to_string(),
                    upper_bound: "O(mn)".to_string(),
                    tight_bound: Some("Θ(mn)".to_string()),
                    proof: Some("需要填充整个表格".to_string()),
                },
                space_complexity: ComplexityBounds {
                    lower_bound: "Ω(mn)".to_string(),
                    upper_bound: "O(mn)".to_string(),
                    tight_bound: Some("Θ(mn)".to_string()),
                    proof: Some("需要存储整个表格".to_string()),
                },
                best_case_analysis: "O(mn)".to_string(),
                average_case_analysis: "O(mn)".to_string(),
                worst_case_analysis: "O(mn)".to_string(),
                amortized_analysis: None,
                practical_performance: "性能稳定，空间开销大".to_string(),
            },
            variants: vec![],
            history: HistoryKnowledge {
                inventor: None,
                year: Some(1970),
                development_history: vec![
                    "1970年代发展".to_string(),
                    "动态规划经典问题".to_string(),
                ],
                milestones: vec![
                    "原始算法".to_string(),
                    "空间优化".to_string(),
                ],
                current_research: vec![
                    "近似算法".to_string(),
                    "并行化研究".to_string(),
                ],
            },
        });
    }

    /// 初始化分类知识
    fn initialize_categories(&mut self) {
        self.categories.insert("排序".to_string(), CategoryKnowledge {
            name: "排序算法".to_string(),
            description: "将数据按照特定顺序排列的算法".to_string(),
            key_algorithms: vec![
                "快速排序".to_string(),
                "归并排序".to_string(),
                "堆排序".to_string(),
                "插入排序".to_string(),
            ],
            common_patterns: vec![
                "比较排序".to_string(),
                "非比较排序".to_string(),
                "稳定排序".to_string(),
                "原地排序".to_string(),
            ],
            design_principles: vec![
                "分治策略".to_string(),
                "贪心策略".to_string(),
                "选择策略".to_string(),
            ],
            applications: vec![
                "数据库查询优化".to_string(),
                "操作系统调度".to_string(),
                "编译器优化".to_string(),
            ],
            learning_path: vec![
                "基础排序算法".to_string(),
                "高级排序算法".to_string(),
                "排序网络".to_string(),
                "外部排序".to_string(),
            ],
        });

        self.categories.insert("搜索".to_string(), CategoryKnowledge {
            name: "搜索算法".to_string(),
            description: "在数据结构中查找特定元素的算法".to_string(),
            key_algorithms: vec![
                "线性搜索".to_string(),
                "二分搜索".to_string(),
                "插值搜索".to_string(),
                "哈希搜索".to_string(),
            ],
            common_patterns: vec![
                "顺序搜索".to_string(),
                "分治搜索".to_string(),
                "概率搜索".to_string(),
            ],
            design_principles: vec![
                "利用数据结构特性".to_string(),
                "减少搜索空间".to_string(),
                "平衡搜索成本".to_string(),
            ],
            applications: vec![
                "数据库索引".to_string(),
                "搜索引擎".to_string(),
                "数值计算".to_string(),
            ],
            learning_path: vec![
                "基础搜索算法".to_string(),
                "高级搜索算法".to_string(),
                "搜索树".to_string(),
                "哈希表".to_string(),
            ],
        });
    }

    /// 初始化应用知识
    fn initialize_applications(&mut self) {
        self.applications.insert("数据库系统".to_string(), ApplicationKnowledge {
            domain: "数据库系统".to_string(),
            description: "数据库管理系统中的算法应用".to_string(),
            algorithms_used: vec![
                "B+树索引".to_string(),
                "哈希索引".to_string(),
                "排序算法".to_string(),
                "查询优化".to_string(),
            ],
            performance_requirements: vec![
                "高并发".to_string(),
                "低延迟".to_string(),
                "高吞吐量".to_string(),
            ],
            implementation_considerations: vec![
                "内存管理".to_string(),
                "磁盘I/O优化".to_string(),
                "并发控制".to_string(),
            ],
            real_world_examples: vec![
                "MySQL".to_string(),
                "PostgreSQL".to_string(),
                "Oracle".to_string(),
            ],
        });

        self.applications.insert("操作系统".to_string(), ApplicationKnowledge {
            domain: "操作系统".to_string(),
            description: "操作系统内核中的算法应用".to_string(),
            algorithms_used: vec![
                "进程调度".to_string(),
                "内存管理".to_string(),
                "文件系统".to_string(),
                "网络协议".to_string(),
            ],
            performance_requirements: vec![
                "实时性".to_string(),
                "公平性".to_string(),
                "效率".to_string(),
            ],
            implementation_considerations: vec![
                "中断处理".to_string(),
                "上下文切换".to_string(),
                "资源管理".to_string(),
            ],
            real_world_examples: vec![
                "Linux内核".to_string(),
                "Windows内核".to_string(),
                "FreeBSD".to_string(),
            ],
        });
    }

    /// 获取算法知识
    pub fn get_algorithm_knowledge(&self, name: &str) -> Option<&AlgorithmKnowledge> {
        self.algorithms.get(name)
    }

    /// 获取分类知识
    pub fn get_category_knowledge(&self, name: &str) -> Option<&CategoryKnowledge> {
        self.categories.get(name)
    }

    /// 获取应用知识
    pub fn get_application_knowledge(&self, name: &str) -> Option<&ApplicationKnowledge> {
        self.applications.get(name)
    }

    /// 获取所有算法名称
    pub fn get_all_algorithm_names(&self) -> Vec<String> {
        self.algorithms.keys().cloned().collect()
    }

    /// 获取所有分类名称
    pub fn get_all_category_names(&self) -> Vec<String> {
        self.categories.keys().cloned().collect()
    }

    /// 获取所有应用名称
    pub fn get_all_application_names(&self) -> Vec<String> {
        self.applications.keys().cloned().collect()
    }

    /// 搜索算法
    pub fn search_algorithms(&self, query: &str) -> Vec<&AlgorithmKnowledge> {
        self.algorithms
            .values()
            .filter(|alg| {
                alg.name.contains(query) ||
                alg.description.contains(query) ||
                alg.category.contains(query)
            })
            .collect()
    }

    /// 生成知识库报告
    pub fn generate_knowledge_report(&self) -> String {
        let mut report = String::new();
        
        report.push_str("=== 算法知识库报告 ===\n\n");
        
        report.push_str(&format!("总算法数: {}\n", self.algorithms.len()));
        report.push_str(&format!("总分类数: {}\n", self.categories.len()));
        report.push_str(&format!("总应用数: {}\n\n", self.applications.len()));
        
        // 按分类统计
        report.push_str("## 按分类统计\n");
        for category in self.categories.values() {
            let count = self.algorithms
                .values()
                .filter(|alg| alg.category == category.name)
                .count();
            report.push_str(&format!("- {}: {} 个算法\n", category.name, count));
        }
        
        report.push_str("\n## 算法列表\n");
        for algorithm in self.algorithms.values() {
            report.push_str(&format!("- {} ({})\n", algorithm.name, algorithm.category));
        }
        
        report.push_str("\n## 应用领域\n");
        for application in self.applications.values() {
            report.push_str(&format!("- {}: {}\n", application.domain, application.description));
        }
        
        report
    }
}
