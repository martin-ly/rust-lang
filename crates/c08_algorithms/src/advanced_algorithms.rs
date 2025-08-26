//! 高级算法实现模块
//! 
//! 本模块提供了Rust中的高级算法实现，包括：
//! - 并行算法
//! - 分布式算法  
//! - 机器学习算法
//! - 密码学算法

use std::sync::{Arc, Mutex};
use std::collections::HashMap;
use rayon::prelude::*;
use rand::Rng;

/// 并行排序算法实现
pub struct ParallelSort;

impl ParallelSort {
    /// 并行快速排序
    pub fn parallel_quicksort<T: Ord + Send + Sync>(arr: &mut [T]) {
        if arr.len() <= 1 {
            return;
        }
        
        let pivot_index = Self::partition(arr);
        let (left, right) = arr.split_at_mut(pivot_index);
        
        // 并行处理左右两部分
        rayon::join(
            || Self::parallel_quicksort(left),
            || Self::parallel_quicksort(&mut right[1..])
        );
    }
    
    /// 并行归并排序
    pub fn parallel_mergesort<T: Ord + Send + Sync + Clone>(arr: &mut [T]) {
        if arr.len() <= 1 {
            return;
        }
        
        let mid = arr.len() / 2;
        let (left, right) = arr.split_at_mut(mid);
        
        // 并行排序左右两部分
        rayon::join(
            || Self::parallel_mergesort(left),
            || Self::parallel_mergesort(right)
        );
        
        // 合并排序结果
        Self::merge(arr, mid);
    }
    
    /// 并行基数排序
    pub fn parallel_radix_sort(arr: &mut [u32]) {
        const RADIX: usize = 256;
        const BITS: usize = 32;
        
        for shift in (0..BITS).step_by(8) {
            let mut counts = vec![0; RADIX];
            
            // 并行计算计数
            for &num in arr.iter() {
                let digit = ((num >> shift) & 0xFF) as usize;
                counts[digit] += 1;
            }
            
            // 计算前缀和
            for i in 1..RADIX {
                counts[i] += counts[i - 1];
            }
            
            // 并行重排
            let mut output = vec![0; arr.len()];
            for (_i, &num) in arr.iter().enumerate() {
                let digit = ((num >> shift) & 0xFF) as usize;
                let pos = counts[digit] - 1;
                output[pos] = num;
                counts[digit] -= 1;
            }
            
            arr.copy_from_slice(&output);
        }
    }
    
    fn partition<T: Ord>(arr: &mut [T]) -> usize {
        let pivot_index = arr.len() - 1;
        let mut i = 0;
        
        for j in 0..pivot_index {
            if arr[j] <= arr[pivot_index] {
                arr.swap(i, j);
                i += 1;
            }
        }
        
        arr.swap(i, pivot_index);
        i
    }
    
    fn merge<T: Ord + Clone>(arr: &mut [T], mid: usize) {
        let left = arr[..mid].to_vec();
        let right = arr[mid..].to_vec();
        
        let mut i = 0;
        let mut j = 0;
        let mut k = 0;
        
        while i < left.len() && j < right.len() {
            if left[i] <= right[j] {
                arr[k] = left[i].clone();
                i += 1;
            } else {
                arr[k] = right[j].clone();
                j += 1;
            }
            k += 1;
        }
        
        while i < left.len() {
            arr[k] = left[i].clone();
            i += 1;
            k += 1;
        }
        
        while j < right.len() {
            arr[k] = right[j].clone();
            j += 1;
            k += 1;
        }
    }
}

/// 分布式算法实现
pub struct DistributedAlgorithms;

impl DistributedAlgorithms {
    /// 分布式MapReduce实现
    pub fn map_reduce<T, U, V, F, G>(
        data: Vec<T>,
        map_fn: F,
        reduce_fn: G,
        num_workers: usize,
    ) -> V
    where
        T: Send + Sync + Clone,
        U: Send + Sync,
        V: Default + Send + Sync,
        F: Fn(T) -> U + Send + Sync,
        G: Fn(V, U) -> V + Send + Sync,
    {
        // 数据分片
        let chunk_size = (data.len() + num_workers - 1) / num_workers;
        let chunks: Vec<Vec<T>> = data
            .chunks(chunk_size)
            .map(|chunk| chunk.to_vec())
            .collect();
        
        // 并行Map阶段
        let mapped_results: Vec<Vec<U>> = chunks
            .into_par_iter()
            .map(|chunk| chunk.into_iter().map(&map_fn).collect())
            .collect();
        
        // Reduce阶段
        let mut result = V::default();
        for mapped_chunk in mapped_results {
            for item in mapped_chunk {
                result = reduce_fn(result, item);
            }
        }
        
        result
    }
}

/// 分布式共识算法 (简化版Paxos)
pub struct PaxosNode {
    #[allow(dead_code)]
    id: usize,
    value: Option<String>,
    accepted_value: Option<String>,
    accepted_proposal: Option<usize>,
    promised_proposal: Option<usize>,
}

impl PaxosNode {
    pub fn new(id: usize) -> Self {
        Self {
            id,
            value: None,
            accepted_value: None,
            accepted_proposal: None,
            promised_proposal: None,
        }
    }
    
    pub fn propose(&mut self, proposal_id: usize, value: String) -> bool {
        if self.promised_proposal.is_none() || 
           self.promised_proposal.unwrap() < proposal_id {
            self.promised_proposal = Some(proposal_id);
            self.value = Some(value);
            true
        } else {
            false
        }
    }
    
    pub fn accept(&mut self, proposal_id: usize, value: String) -> bool {
        if self.promised_proposal.is_none() || 
           self.promised_proposal.unwrap() <= proposal_id {
            self.accepted_proposal = Some(proposal_id);
            self.accepted_value = Some(value);
            true
        } else {
            false
        }
    }
}

/// 分布式哈希表 (DHT) 实现
pub struct DistributedHashTable<K, V> {
    nodes: HashMap<u64, Arc<Mutex<HashMap<K, V>>>>,
    num_nodes: usize,
}

impl<K, V> DistributedHashTable<K, V>
where
    K: Clone + Send + Sync + std::hash::Hash + Eq,
    V: Clone + Send + Sync,
{
    pub fn new(num_nodes: usize) -> Self {
        let mut nodes = HashMap::new();
        for i in 0..num_nodes {
            nodes.insert(i as u64, Arc::new(Mutex::new(HashMap::new())));
        }
        
        Self { nodes, num_nodes }
    }
    
    pub fn put(&self, key: K, value: V) {
        let node_id = self.hash_key(&key);
        if let Some(node) = self.nodes.get(&node_id) {
            if let Ok(mut node_data) = node.lock() {
                node_data.insert(key, value);
            }
        }
    }
    
    pub fn get(&self, key: &K) -> Option<V> {
        let node_id = self.hash_key(key);
        if let Some(node) = self.nodes.get(&node_id) {
            if let Ok(node_data) = node.lock() {
                node_data.get(key).cloned()
            } else {
                None
            }
        } else {
            None
        }
    }
    
    fn hash_key(&self, key: &K) -> u64 {
        // 简化的哈希函数
        use std::collections::hash_map::DefaultHasher;
        use std::hash::Hasher;
        
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish() % self.num_nodes as u64
    }
}

/// 线性回归实现
pub struct LinearRegression {
    weights: Vec<f64>,
    bias: f64,
    learning_rate: f64,
}

impl LinearRegression {
    pub fn new(input_size: usize, learning_rate: f64) -> Self {
        Self {
            weights: vec![0.0; input_size],
            bias: 0.0,
            learning_rate,
        }
    }
    
    pub fn train(&mut self, features: &[Vec<f64>], targets: &[f64], epochs: usize) {
        for _ in 0..epochs {
            for (feature, &target) in features.iter().zip(targets.iter()) {
                let prediction = self.predict(feature);
                let error = target - prediction;
                
                // 更新权重
                for (weight, &feature_val) in self.weights.iter_mut().zip(feature.iter()) {
                    *weight += self.learning_rate * error * feature_val;
                }
                
                // 更新偏置
                self.bias += self.learning_rate * error;
            }
        }
    }
    
    pub fn predict(&self, features: &[f64]) -> f64 {
        let mut result = self.bias;
        for (weight, &feature) in self.weights.iter().zip(features.iter()) {
            result += weight * feature;
        }
        result
    }
}

/// K-means聚类算法
pub struct KMeans {
    k: usize,
    centroids: Vec<Vec<f64>>,
    max_iterations: usize,
}

impl KMeans {
    pub fn new(k: usize, max_iterations: usize) -> Self {
        Self {
            k,
            centroids: Vec::new(),
            max_iterations,
        }
    }
    
    pub fn fit(&mut self, data: &[Vec<f64>]) -> Vec<usize> {
        // 初始化聚类中心
        self.initialize_centroids(data);
        
        let mut assignments = vec![0; data.len()];
        
        for _ in 0..self.max_iterations {
            let mut new_assignments = vec![0; data.len()];
            let mut cluster_sums = vec![vec![0.0; data[0].len()]; self.k];
            let mut cluster_counts = vec![0; self.k];
            
            // 分配点到最近的聚类中心
            for (i, point) in data.iter().enumerate() {
                let cluster = self.find_nearest_centroid(point);
                new_assignments[i] = cluster;
                
                for (j, &val) in point.iter().enumerate() {
                    cluster_sums[cluster][j] += val;
                }
                cluster_counts[cluster] += 1;
            }
            
            // 更新聚类中心
            for i in 0..self.k {
                if cluster_counts[i] > 0 {
                    for j in 0..self.centroids[i].len() {
                        self.centroids[i][j] = cluster_sums[i][j] / cluster_counts[i] as f64;
                    }
                }
            }
            
            // 检查收敛
            if assignments == new_assignments {
                break;
            }
            assignments = new_assignments;
        }
        
        assignments
    }
    
    fn initialize_centroids(&mut self, data: &[Vec<f64>]) {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        self.centroids.clear();
        for _ in 0..self.k {
            let random_index = rng.gen_range(0..data.len());
            self.centroids.push(data[random_index].clone());
        }
    }
    
    fn find_nearest_centroid(&self, point: &[f64]) -> usize {
        let mut min_distance = f64::INFINITY;
        let mut nearest_cluster = 0;
        
        for (i, centroid) in self.centroids.iter().enumerate() {
            let distance = self.euclidean_distance(point, centroid);
            if distance < min_distance {
                min_distance = distance;
                nearest_cluster = i;
            }
        }
        
        nearest_cluster
    }
    
    fn euclidean_distance(&self, a: &[f64], b: &[f64]) -> f64 {
        a.iter()
            .zip(b.iter())
            .map(|(x, y)| (x - y).powi(2))
            .sum::<f64>()
            .sqrt()
    }
}

/// 决策树实现
pub struct DecisionTree {
    root: Option<Box<TreeNode>>,
    max_depth: usize,
}

struct TreeNode {
    feature_index: Option<usize>,
    threshold: Option<f64>,
    value: Option<f64>,
    left: Option<Box<TreeNode>>,
    right: Option<Box<TreeNode>>,
}

impl DecisionTree {
    pub fn new(max_depth: usize) -> Self {
        Self {
            root: None,
            max_depth,
        }
    }
    
    pub fn fit(&mut self, features: &[Vec<f64>], targets: &[f64]) {
        self.root = Some(self.build_tree(features, targets, 0));
    }
    
    pub fn predict(&self, features: &[f64]) -> f64 {
        if let Some(ref root) = self.root {
            self.predict_recursive(root, features)
        } else {
            0.0
        }
    }
    
    fn build_tree(&self, features: &[Vec<f64>], targets: &[f64], depth: usize) -> Box<TreeNode> {
        if depth >= self.max_depth || targets.iter().all(|&t| t == targets[0]) {
            return Box::new(TreeNode {
                feature_index: None,
                threshold: None,
                value: Some(targets.iter().sum::<f64>() / targets.len() as f64),
                left: None,
                right: None,
            });
        }
        
        let (best_feature, best_threshold) = self.find_best_split(features, targets);
        
        if best_feature.is_none() {
            return Box::new(TreeNode {
                feature_index: None,
                threshold: None,
                value: Some(targets.iter().sum::<f64>() / targets.len() as f64),
                left: None,
                right: None,
            });
        }
        
        let feature_index = best_feature.unwrap();
        let threshold = best_threshold.unwrap();
        
        let mut left_features = Vec::new();
        let mut left_targets = Vec::new();
        let mut right_features = Vec::new();
        let mut right_targets = Vec::new();
        
        for (feature, &target) in features.iter().zip(targets.iter()) {
            if feature[feature_index] <= threshold {
                left_features.push(feature.clone());
                left_targets.push(target);
            } else {
                right_features.push(feature.clone());
                right_targets.push(target);
            }
        }
        
        Box::new(TreeNode {
            feature_index: Some(feature_index),
            threshold: Some(threshold),
            value: None,
            left: Some(self.build_tree(&left_features, &left_targets, depth + 1)),
            right: Some(self.build_tree(&right_features, &right_targets, depth + 1)),
        })
    }
    
    fn find_best_split(&self, features: &[Vec<f64>], targets: &[f64]) -> (Option<usize>, Option<f64>) {
        let mut best_gain = 0.0;
        let mut best_feature = None;
        let mut best_threshold = None;
        
        for feature_index in 0..features[0].len() {
            let mut values: Vec<f64> = features.iter().map(|f| f[feature_index]).collect();
            values.sort_by(|a, b| a.partial_cmp(b).unwrap());
            
            for i in 0..values.len() - 1 {
                let threshold = (values[i] + values[i + 1]) / 2.0;
                let gain = self.calculate_information_gain(features, targets, feature_index, threshold);
                
                if gain > best_gain {
                    best_gain = gain;
                    best_feature = Some(feature_index);
                    best_threshold = Some(threshold);
                }
            }
        }
        
        (best_feature, best_threshold)
    }
    
    fn calculate_information_gain(&self, features: &[Vec<f64>], targets: &[f64], feature_index: usize, threshold: f64) -> f64 {
        let parent_entropy = self.calculate_entropy(targets);
        
        let mut left_targets = Vec::new();
        let mut right_targets = Vec::new();
        
        for (feature, &target) in features.iter().zip(targets.iter()) {
            if feature[feature_index] <= threshold {
                left_targets.push(target);
            } else {
                right_targets.push(target);
            }
        }
        
        let left_entropy = self.calculate_entropy(&left_targets);
        let right_entropy = self.calculate_entropy(&right_targets);
        
        let left_weight = left_targets.len() as f64 / targets.len() as f64;
        let right_weight = right_targets.len() as f64 / targets.len() as f64;
        
        parent_entropy - (left_weight * left_entropy + right_weight * right_entropy)
    }
    
    fn calculate_entropy(&self, targets: &[f64]) -> f64 {
        if targets.is_empty() {
            return 0.0;
        }
        
        let mean = targets.iter().sum::<f64>() / targets.len() as f64;
        let variance = targets.iter().map(|&t| (t - mean).powi(2)).sum::<f64>() / targets.len() as f64;
        
        if variance == 0.0 {
            0.0
        } else {
            0.5 * (2.0 * std::f64::consts::PI * std::f64::consts::E * variance).ln()
        }
    }
    
    fn predict_recursive(&self, node: &TreeNode, features: &[f64]) -> f64 {
        if let Some(value) = node.value {
            return value;
        }
        
        if let (Some(feature_index), Some(threshold)) = (node.feature_index, node.threshold) {
            if features[feature_index] <= threshold {
                if let Some(ref left) = node.left {
                    self.predict_recursive(left, features)
                } else {
                    0.0
                }
            } else {
                if let Some(ref right) = node.right {
                    self.predict_recursive(right, features)
                } else {
                    0.0
                }
            }
        } else {
            0.0
        }
    }
}

/// 密码学算法实现
pub struct CryptographicAlgorithms;

/// RSA加密算法实现
pub struct RSA {
    public_key: (u64, u64),
    private_key: (u64, u64),
}

impl RSA {
    pub fn new(bit_length: usize) -> Self {
        // 生成大素数
        let p = Self::generate_prime(bit_length / 2);
        let q = Self::generate_prime(bit_length / 2);
        
        // 使用更安全的中间宽度避免乘法溢出
        let n = ((p as u128) * (q as u128)) as u64;
        let phi = ((p as u128 - 1) * (q as u128 - 1)) as u64;
        
        // 选择公钥指数
        let e = 65537; // 常用的公钥指数
        
        // 计算私钥指数
        let d = Self::mod_inverse(e, phi);
        
        Self {
            public_key: (e, n),
            private_key: (d, n),
        }
    }
    
    pub fn encrypt(&self, message: u64) -> u64 {
        Self::mod_pow(message, self.public_key.0, self.public_key.1)
    }
    
    pub fn decrypt(&self, ciphertext: u64) -> u64 {
        Self::mod_pow(ciphertext, self.private_key.0, self.private_key.1)
    }
    
    fn generate_prime(bits: usize) -> u64 {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        loop {
            if bits == 0 { return 2; }
            // 取区间 [2^(bits-1), 2^bits)，保证乘积在 u64 范围内（当 overall bit_length=2*bits）
            let low = 1u64 << (bits as u32 - 1);
            let high = 1u64 << (bits as u32);
            let candidate = rng.gen_range(low..high);
            if Self::is_prime(candidate) {
                return candidate;
            }
        }
    }
    
    fn is_prime(n: u64) -> bool {
        if n < 2 {
            return false;
        }
        if n == 2 {
            return true;
        }
        if n % 2 == 0 {
            return false;
        }
        
        let mut d = n - 1;
        let mut s = 0;
        while d % 2 == 0 {
            d /= 2;
            s += 1;
        }
        
        // Miller-Rabin素性测试
        for _ in 0..5 {
            let a = rand::thread_rng().gen_range(2..n);
            let mut x = Self::mod_pow(a, d, n);
            
            if x == 1 || x == n - 1 {
                continue;
            }
            
            let mut is_composite = true;
            for _ in 0..s - 1 {
                x = (((x as u128) * (x as u128)) % (n as u128)) as u64;
                if x == n - 1 {
                    is_composite = false;
                    break;
                }
            }
            
            if is_composite {
                return false;
            }
        }
        
        true
    }
    
    fn mod_pow(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
        let mut result: u64 = 1;
        if modulus == 1 { return 0; }
        base %= modulus;

        while exponent > 0 {
            if (exponent & 1) == 1 {
                let tmp = ((result as u128) * (base as u128)) % (modulus as u128);
                result = tmp as u64;
            }
            let tmp = ((base as u128) * (base as u128)) % (modulus as u128);
            base = tmp as u64;
            exponent >>= 1;
        }

        result
    }
    
    fn mod_inverse(a: u64, m: u64) -> u64 {
        // 扩展欧几里得算法（使用有符号整型避免无符号下溢）
        fn egcd(a: i128, b: i128) -> (i128, i128, i128) {
            if b == 0 {
                (a, 1, 0)
            } else {
                let (g, x, y) = egcd(b, a % b);
                (g, y, x - (a / b) * y)
            }
        }

        let a_i = (a % m) as i128;
        let m_i = m as i128;
        let (g, x, _) = egcd(a_i, m_i);
        if g != 1 {
            panic!("Modular inverse does not exist");
        }
        // 归一化到 [0, m)
        let mut inv = x % m_i;
        if inv < 0 { inv += m_i; }
        inv as u64
    }
}

/// AES加密算法实现 (简化版)
pub struct AES {
    key: [u8; 16],
    round_keys: [[u8; 16]; 11],
}

impl AES {
    pub fn new(key: [u8; 16]) -> Self {
        let mut aes = Self {
            key,
            round_keys: [[0; 16]; 11],
        };
        aes.key_expansion();
        aes
    }
    
    pub fn encrypt(&self, plaintext: [u8; 16]) -> [u8; 16] {
        let mut state = plaintext;
        
        // 初始轮密钥加
        Self::add_round_key(&mut state, &self.round_keys[0]);
        
        // 9个主轮
        for round in 1..10 {
            Self::sub_bytes(&mut state);
            Self::shift_rows(&mut state);
            Self::mix_columns(&mut state);
            Self::add_round_key(&mut state, &self.round_keys[round]);
        }
        
        // 最后一轮
        Self::sub_bytes(&mut state);
        Self::shift_rows(&mut state);
        Self::add_round_key(&mut state, &self.round_keys[10]);
        
        state
    }
    
    pub fn decrypt(&self, ciphertext: [u8; 16]) -> [u8; 16] {
        let mut state = ciphertext;
        
        // 初始轮密钥加
        Self::add_round_key(&mut state, &self.round_keys[10]);
        
        // 9个主轮
        for round in (1..10).rev() {
            Self::inv_shift_rows(&mut state);
            Self::inv_sub_bytes(&mut state);
            Self::add_round_key(&mut state, &self.round_keys[round]);
            Self::inv_mix_columns(&mut state);
        }
        
        // 最后一轮
        Self::inv_shift_rows(&mut state);
        Self::inv_sub_bytes(&mut state);
        Self::add_round_key(&mut state, &self.round_keys[0]);
        
        state
    }
    
    fn key_expansion(&mut self) {
        // 简化的密钥扩展
        for i in 0..11 {
            for j in 0..16 {
                self.round_keys[i][j] = self.key[j] ^ (i as u8);
            }
        }
    }
    
    fn sub_bytes(state: &mut [u8; 16]) {
        // 简化的S盒替换
        for byte in state.iter_mut() {
            *byte = (*byte + 1) % 255;
        }
    }
    
    fn inv_sub_bytes(state: &mut [u8; 16]) {
        // 简化的逆S盒替换
        for byte in state.iter_mut() {
            *byte = (*byte + 254) % 255;
        }
    }
    
    fn shift_rows(state: &mut [u8; 16]) {
        // 行移位
        let temp = state[1];
        state[1] = state[5];
        state[5] = state[9];
        state[9] = state[13];
        state[13] = temp;
        
        let temp1 = state[2];
        let temp2 = state[6];
        state[2] = state[10];
        state[6] = state[14];
        state[10] = temp1;
        state[14] = temp2;
        
        let temp = state[15];
        state[15] = state[11];
        state[11] = state[7];
        state[7] = state[3];
        state[3] = temp;
    }
    
    fn inv_shift_rows(state: &mut [u8; 16]) {
        // 逆行移位
        let temp = state[13];
        state[13] = state[9];
        state[9] = state[5];
        state[5] = state[1];
        state[1] = temp;
        
        let temp1 = state[10];
        let temp2 = state[14];
        state[10] = state[2];
        state[14] = state[6];
        state[2] = temp1;
        state[6] = temp2;
        
        let temp = state[3];
        state[3] = state[7];
        state[7] = state[11];
        state[11] = state[15];
        state[15] = temp;
    }
    
    fn mix_columns(state: &mut [u8; 16]) {
        // 简化的列混合
        for i in 0..4 {
            let col_start = i * 4;
            let temp = state[col_start];
            state[col_start] = state[col_start + 1];
            state[col_start + 1] = state[col_start + 2];
            state[col_start + 2] = state[col_start + 3];
            state[col_start + 3] = temp;
        }
    }
    
    fn inv_mix_columns(state: &mut [u8; 16]) {
        // 简化的逆列混合
        for i in 0..4 {
            let col_start = i * 4;
            let temp = state[col_start + 3];
            state[col_start + 3] = state[col_start + 2];
            state[col_start + 2] = state[col_start + 1];
            state[col_start + 1] = state[col_start];
            state[col_start] = temp;
        }
    }
    
    fn add_round_key(state: &mut [u8; 16], round_key: &[u8; 16]) {
        for i in 0..16 {
            state[i] ^= round_key[i];
        }
    }
}

/// SHA-256哈希算法实现
pub struct SHA256 {
    state: [u32; 8],
}

impl SHA256 {
    pub fn new() -> Self {
        Self {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
            ],
        }
    }
    
    pub fn hash(&mut self, data: &[u8]) -> [u8; 32] {
        let mut message = data.to_vec();
        let original_length = message.len() * 8;
        
        // 填充
        message.push(0x80);
        while (message.len() + 8) % 64 != 0 {
            message.push(0x00);
        }
        
        // 添加长度
        for i in 0..8 {
            message.push(((original_length >> (56 - i * 8)) & 0xFF) as u8);
        }
        
        // 处理每个512位块
        for chunk in message.chunks(64) {
            self.process_block(chunk);
        }
        
        // 返回哈希值
        let mut result = [0u8; 32];
        for i in 0..8 {
            let bytes = self.state[i].to_be_bytes();
            result[i * 4..(i + 1) * 4].copy_from_slice(&bytes);
        }
        result
    }
    
    fn process_block(&mut self, block: &[u8]) {
        let mut w = [0u32; 64];
        
        // 准备消息调度
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                block[i * 4],
                block[i * 4 + 1],
                block[i * 4 + 2],
                block[i * 4 + 3],
            ]);
        }
        
        for i in 16..64 {
            let s0 = Self::right_rotate(w[i - 15], 7) ^ Self::right_rotate(w[i - 15], 18) ^ (w[i - 15] >> 3);
            let s1 = Self::right_rotate(w[i - 2], 17) ^ Self::right_rotate(w[i - 2], 19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        }
        
        let mut a = self.state[0];
        let mut b = self.state[1];
        let mut c = self.state[2];
        let mut d = self.state[3];
        let mut e = self.state[4];
        let mut f = self.state[5];
        let mut g = self.state[6];
        let mut h = self.state[7];
        
        // 主循环
        for i in 0..64 {
            let s1 = Self::right_rotate(e, 6) ^ Self::right_rotate(e, 11) ^ Self::right_rotate(e, 25);
            let ch = (e & f) ^ (!e & g);
            let temp1 = h.wrapping_add(s1).wrapping_add(ch).wrapping_add(Self::K[i]).wrapping_add(w[i]);
            let s0 = Self::right_rotate(a, 2) ^ Self::right_rotate(a, 13) ^ Self::right_rotate(a, 22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        
        // 更新状态
        self.state[0] = self.state[0].wrapping_add(a);
        self.state[1] = self.state[1].wrapping_add(b);
        self.state[2] = self.state[2].wrapping_add(c);
        self.state[3] = self.state[3].wrapping_add(d);
        self.state[4] = self.state[4].wrapping_add(e);
        self.state[5] = self.state[5].wrapping_add(f);
        self.state[6] = self.state[6].wrapping_add(g);
        self.state[7] = self.state[7].wrapping_add(h);
    }
    
    fn right_rotate(value: u32, shift: u32) -> u32 {
        (value >> shift) | (value << (32 - shift))
    }
    
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
        0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
        0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
        0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
        0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_parallel_sort() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5];
        let mut expected = arr.clone();
        expected.sort();
        
        ParallelSort::parallel_quicksort(&mut arr);
        assert_eq!(arr, expected);
    }
    
    #[test]
    fn test_linear_regression() {
        let features = vec![
            vec![1.0, 2.0],
            vec![2.0, 3.0],
            vec![3.0, 4.0],
            vec![4.0, 5.0],
        ];
        let targets = vec![2.0, 4.0, 6.0, 8.0];
        
        let mut model = LinearRegression::new(2, 0.01);
        model.train(&features, &targets, 1000);
        
        let prediction = model.predict(&[5.0, 6.0]);
        assert!(prediction > 9.0 && prediction < 11.0);
    }
    
    #[test]
    fn test_rsa_encryption() {
        let rsa = RSA::new(64);
        let message = 12345;
        
        let encrypted = rsa.encrypt(message);
        let decrypted = rsa.decrypt(encrypted);
        
        assert_eq!(message, decrypted);
    }
    
    #[test]
    fn test_sha256() {
        let mut sha256 = SHA256::new();
        let data = b"Hello, World!";
        let hash = sha256.hash(data);
        
        assert_eq!(hash.len(), 32);
        assert_ne!(hash, [0u8; 32]);
    }
}
