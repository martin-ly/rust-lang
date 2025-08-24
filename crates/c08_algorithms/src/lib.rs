//! Rust高级算法实现库
//! 
//! 本库提供了Rust中的高级算法实现，包括：
//! - 并行算法
//! - 分布式算法
//! - 机器学习算法
//! - 密码学算法

pub mod parallel_algorithms;
pub mod machine_learning;
pub mod cryptographic_algorithms;

// 重新导出主要类型
pub use parallel_algorithms::{ParallelSort, ParallelSearch, ParallelGraph};
pub use machine_learning::{LinearRegression, KMeans, DecisionTree, NaiveBayes, SupportVectorMachine};
pub use cryptographic_algorithms::{RSA, AES, SHA256, EllipticCurve, DigitalSignature};

/// 算法性能基准测试
pub mod benchmarks {
    use super::*;
    use std::time::Instant;
    
    /// 并行排序性能测试
    pub fn benchmark_parallel_sort() {
        let mut data: Vec<i32> = (0..100000).rev().collect();
        let mut data_sequential = data.clone();
        
        // 并行排序
        let start = Instant::now();
        ParallelSort::parallel_quicksort(&mut data);
        let parallel_time = start.elapsed();
        
        // 顺序排序
        let start = Instant::now();
        data_sequential.sort();
        let sequential_time = start.elapsed();
        
        println!("并行排序时间: {:?}", parallel_time);
        println!("顺序排序时间: {:?}", sequential_time);
        println!("加速比: {:.2}x", sequential_time.as_nanos() as f64 / parallel_time.as_nanos() as f64);
    }
    
    /// 机器学习算法性能测试
    pub fn benchmark_ml_algorithms() {
        // 生成测试数据
        let features: Vec<Vec<f64>> = (0..1000)
            .map(|i| vec![i as f64, (i * 2) as f64])
            .collect();
        let targets: Vec<f64> = (0..1000).map(|i| (i * 3) as f64).collect();
        
        // 线性回归测试
        let start = Instant::now();
        let mut lr = LinearRegression::new(2, 0.01);
        lr.train(&features, &targets, 100);
        let lr_time = start.elapsed();
        
        // K-means测试
        let start = Instant::now();
        let mut kmeans = KMeans::new(3, 100);
        kmeans.fit(&features);
        let kmeans_time = start.elapsed();
        
        println!("线性回归训练时间: {:?}", lr_time);
        println!("K-means聚类时间: {:?}", kmeans_time);
    }
    
    /// 密码学算法性能测试
    pub fn benchmark_crypto_algorithms() {
        let data = b"Hello, World! This is a test message for cryptographic benchmarking.";
        
        // SHA-256测试
        let start = Instant::now();
        let mut sha256 = SHA256::new();
        for _ in 0..10000 {
            sha256.hash(data);
        }
        let sha256_time = start.elapsed();
        
        // RSA测试
        let start = Instant::now();
        let rsa = RSA::new(512);
        let message = 12345u64;
        for _ in 0..100 {
            let encrypted = rsa.encrypt(message);
            let _decrypted = rsa.decrypt(encrypted);
        }
        let rsa_time = start.elapsed();
        
        println!("SHA-256 10000次哈希时间: {:?}", sha256_time);
        println!("RSA 100次加密解密时间: {:?}", rsa_time);
    }
}

/// 算法复杂度分析
pub mod complexity_analysis {
    use std::collections::HashMap;
    
    /// 算法复杂度类型
    #[derive(Debug, Clone, PartialEq)]
    pub enum Complexity {
        O1,      // 常数时间
        OLogN,   // 对数时间
        ON,      // 线性时间
        ONLogN,  // 线性对数时间
        ON2,     // 平方时间
        ON3,     // 立方时间
        O2N,     // 指数时间
        ONFactorial, // 阶乘时间
    }
    
    /// 算法复杂度分析器
    pub struct ComplexityAnalyzer {
        complexities: HashMap<String, Complexity>,
    }
    
    impl ComplexityAnalyzer {
        pub fn new() -> Self {
            let mut complexities = HashMap::new();
            
            // 并行算法复杂度
            complexities.insert("parallel_quicksort".to_string(), Complexity::ONLogN);
            complexities.insert("parallel_mergesort".to_string(), Complexity::ONLogN);
            complexities.insert("parallel_radix_sort".to_string(), Complexity::ON);
            complexities.insert("parallel_binary_search".to_string(), Complexity::OLogN);
            complexities.insert("parallel_linear_search".to_string(), Complexity::ON);
            complexities.insert("parallel_bfs".to_string(), Complexity::OVE);
            complexities.insert("parallel_dfs".to_string(), Complexity::OVE);
            
            // 机器学习算法复杂度
            complexities.insert("linear_regression".to_string(), Complexity::ON);
            complexities.insert("kmeans".to_string(), Complexity::ONK);
            complexities.insert("decision_tree".to_string(), Complexity::ONLogN);
            complexities.insert("naive_bayes".to_string(), Complexity::ON);
            complexities.insert("svm".to_string(), Complexity::ON2);
            
            // 密码学算法复杂度
            complexities.insert("rsa_encryption".to_string(), Complexity::ON3);
            complexities.insert("aes_encryption".to_string(), Complexity::ON);
            complexities.insert("sha256".to_string(), Complexity::ON);
            complexities.insert("elliptic_curve".to_string(), Complexity::ON2);
            
            Self { complexities }
        }
        
        pub fn get_complexity(&self, algorithm: &str) -> Option<&Complexity> {
            self.complexities.get(algorithm)
        }
        
        pub fn add_complexity(&mut self, algorithm: String, complexity: Complexity) {
            self.complexities.insert(algorithm, complexity);
        }
        
        pub fn compare_complexity(&self, algo1: &str, algo2: &str) -> Option<std::cmp::Ordering> {
            let comp1 = self.complexities.get(algo1)?;
            let comp2 = self.complexities.get(algo2)?;
            
            Some(self.complexity_to_value(comp1).cmp(&self.complexity_to_value(comp2)))
        }
        
        fn complexity_to_value(&self, complexity: &Complexity) -> u8 {
            match complexity {
                Complexity::O1 => 1,
                Complexity::OLogN => 2,
                Complexity::ON => 3,
                Complexity::ONLogN => 4,
                Complexity::ON2 => 5,
                Complexity::ON3 => 6,
                Complexity::O2N => 7,
                Complexity::ONFactorial => 8,
            }
        }
    }
    
    /// 性能分析器
    pub struct PerformanceAnalyzer {
        measurements: HashMap<String, Vec<f64>>,
    }
    
    impl PerformanceAnalyzer {
        pub fn new() -> Self {
            Self {
                measurements: HashMap::new(),
            }
        }
        
        pub fn add_measurement(&mut self, algorithm: String, time_ms: f64) {
            self.measurements
                .entry(algorithm)
                .or_insert_with(Vec::new)
                .push(time_ms);
        }
        
        pub fn get_average_time(&self, algorithm: &str) -> Option<f64> {
            self.measurements.get(algorithm).map(|times| {
                times.iter().sum::<f64>() / times.len() as f64
            })
        }
        
        pub fn get_best_time(&self, algorithm: &str) -> Option<f64> {
            self.measurements.get(algorithm).map(|times| {
                *times.iter().min_by(|a, b| a.partial_cmp(b).unwrap()).unwrap()
            })
        }
        
        pub fn get_worst_time(&self, algorithm: &str) -> Option<f64> {
            self.measurements.get(algorithm).map(|times| {
                *times.iter().max_by(|a, b| a.partial_cmp(b).unwrap()).unwrap()
            })
        }
        
        pub fn compare_algorithms(&self, algo1: &str, algo2: &str) -> Option<f64> {
            let avg1 = self.get_average_time(algo1)?;
            let avg2 = self.get_average_time(algo2)?;
            
            Some(avg1 / avg2)
        }
    }
}

/// 算法可视化工具
pub mod visualization {
    use std::collections::HashMap;
    
    /// 算法执行步骤记录器
    pub struct StepRecorder {
        steps: Vec<Step>,
        current_step: usize,
    }
    
    #[derive(Debug, Clone)]
    pub struct Step {
        pub step_number: usize,
        pub algorithm: String,
        pub operation: String,
        pub data_state: String,
        pub time_ms: f64,
    }
    
    impl StepRecorder {
        pub fn new() -> Self {
            Self {
                steps: Vec::new(),
                current_step: 0,
            }
        }
        
        pub fn record_step(&mut self, algorithm: String, operation: String, data_state: String, time_ms: f64) {
            self.current_step += 1;
            self.steps.push(Step {
                step_number: self.current_step,
                algorithm,
                operation,
                data_state,
                time_ms,
            });
        }
        
        pub fn get_steps(&self) -> &[Step] {
            &self.steps
        }
        
        pub fn clear(&mut self) {
            self.steps.clear();
            self.current_step = 0;
        }
        
        pub fn export_to_json(&self) -> String {
            // 简化的JSON导出
            let mut json = String::from("[");
            for (i, step) in self.steps.iter().enumerate() {
                if i > 0 {
                    json.push(',');
                }
                json.push_str(&format!(
                    r#"{{"step":{},"algorithm":"{}","operation":"{}","data":"{}","time":{}}}"#,
                    step.step_number, step.algorithm, step.operation, step.data_state, step.time_ms
                ));
            }
            json.push(']');
            json
        }
    }
    
    /// 算法执行树可视化
    pub struct ExecutionTree {
        nodes: HashMap<usize, TreeNode>,
        next_id: usize,
    }
    
    #[derive(Debug, Clone)]
    pub struct TreeNode {
        pub id: usize,
        pub parent_id: Option<usize>,
        pub operation: String,
        pub data_size: usize,
        pub execution_time: f64,
        pub children: Vec<usize>,
    }
    
    impl ExecutionTree {
        pub fn new() -> Self {
            Self {
                nodes: HashMap::new(),
                next_id: 0,
            }
        }
        
        pub fn add_node(&mut self, parent_id: Option<usize>, operation: String, data_size: usize, execution_time: f64) -> usize {
            let id = self.next_id;
            self.next_id += 1;
            
            let node = TreeNode {
                id,
                parent_id,
                operation,
                data_size,
                execution_time,
                children: Vec::new(),
            };
            
            self.nodes.insert(id, node);
            
            if let Some(parent_id) = parent_id {
                if let Some(parent) = self.nodes.get_mut(&parent_id) {
                    parent.children.push(id);
                }
            }
            
            id
        }
        
        pub fn get_node(&self, id: usize) -> Option<&TreeNode> {
            self.nodes.get(&id)
        }
        
        pub fn get_root_nodes(&self) -> Vec<&TreeNode> {
            self.nodes.values().filter(|node| node.parent_id.is_none()).collect()
        }
        
        pub fn get_total_execution_time(&self) -> f64 {
            self.nodes.values().map(|node| node.execution_time).sum()
        }
        
        pub fn get_max_depth(&self) -> usize {
            self.calculate_depth(&self.get_root_nodes())
        }
        
        fn calculate_depth(&self, nodes: &[&TreeNode]) -> usize {
            if nodes.is_empty() {
                return 0;
            }
            
            let mut max_depth = 0;
            for node in nodes {
                let children: Vec<&TreeNode> = node.children.iter()
                    .filter_map(|&id| self.nodes.get(&id))
                    .collect();
                let depth = 1 + self.calculate_depth(&children);
                max_depth = max_depth.max(depth);
            }
            
            max_depth
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_complexity_analyzer() {
        let analyzer = complexity_analysis::ComplexityAnalyzer::new();
        
        assert_eq!(analyzer.get_complexity("parallel_quicksort"), Some(&complexity_analysis::Complexity::ONLogN));
        assert_eq!(analyzer.get_complexity("linear_regression"), Some(&complexity_analysis::Complexity::ON));
    }
    
    #[test]
    fn test_performance_analyzer() {
        let mut analyzer = complexity_analysis::PerformanceAnalyzer::new();
        
        analyzer.add_measurement("algo1".to_string(), 10.0);
        analyzer.add_measurement("algo1".to_string(), 12.0);
        analyzer.add_measurement("algo2".to_string(), 20.0);
        
        assert_eq!(analyzer.get_average_time("algo1"), Some(11.0));
        assert_eq!(analyzer.get_best_time("algo1"), Some(10.0));
        assert_eq!(analyzer.get_worst_time("algo1"), Some(12.0));
    }
    
    #[test]
    fn test_step_recorder() {
        let mut recorder = visualization::StepRecorder::new();
        
        recorder.record_step(
            "quicksort".to_string(),
            "partition".to_string(),
            "[3,1,4,1,5]".to_string(),
            1.5,
        );
        
        let steps = recorder.get_steps();
        assert_eq!(steps.len(), 1);
        assert_eq!(steps[0].algorithm, "quicksort");
    }
    
    #[test]
    fn test_execution_tree() {
        let mut tree = visualization::ExecutionTree::new();
        
        let root_id = tree.add_node(None, "start".to_string(), 100, 0.0);
        let child_id = tree.add_node(Some(root_id), "process".to_string(), 50, 1.0);
        
        assert_eq!(tree.get_node(root_id).unwrap().children.len(), 1);
        assert_eq!(tree.get_node(child_id).unwrap().parent_id, Some(root_id));
    }
}
