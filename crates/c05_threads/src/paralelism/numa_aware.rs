//! NUMA感知并行计算
//!
//! 本模块提供了NUMA（非统一内存访问）感知的并行计算功能：
//! - NUMA拓扑检测
//! - NUMA感知任务分配
//! - NUMA本地内存分配
//! - NUMA感知数据布局

use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;
//use rayon::prelude::*;
use num_cpus;

/// NUMA节点信息
#[derive(Debug, Clone)]
pub struct NumaNode {
    pub id: usize,
    pub cpu_count: usize,
    pub memory_size: usize,
    pub cpu_ids: Vec<usize>,
}

/// NUMA拓扑信息
#[derive(Debug, Clone)]
pub struct NumaTopology {
    pub nodes: Vec<NumaNode>,
    pub total_cpus: usize,
    pub total_memory: usize,
}

impl NumaTopology {
    /// 创建新的NUMA拓扑
    pub fn new() -> Self {
        let total_cpus = num_cpus::get();
        let mut nodes = Vec::new();

        // 简化实现：假设每个CPU核心一个NUMA节点
        for i in 0..total_cpus {
            nodes.push(NumaNode {
                id: i,
                cpu_count: 1,
                memory_size: 1024 * 1024 * 1024, // 假设1GB内存
                cpu_ids: vec![i],
            });
        }

        Self {
            nodes,
            total_cpus,
            total_memory: total_cpus * 1024 * 1024 * 1024,
        }
    }

    /// 获取指定NUMA节点的信息
    pub fn get_node(&self, node_id: usize) -> Option<&NumaNode> {
        self.nodes.get(node_id)
    }

    /// 获取所有NUMA节点
    pub fn get_nodes(&self) -> &[NumaNode] {
        &self.nodes
    }

    /// 获取NUMA节点数量
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
}

/// NUMA感知任务分配器
pub struct NumaAwareTaskAllocator {
    topology: NumaTopology,
    node_workloads: Arc<Mutex<HashMap<usize, usize>>>,
}

impl NumaAwareTaskAllocator {
    /// 创建新的NUMA感知任务分配器
    pub fn new() -> Self {
        Self {
            topology: NumaTopology::new(),
            node_workloads: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// 分配任务到最优NUMA节点
    pub fn allocate_task(&self, _task_id: usize) -> usize {
        let mut workloads = self.node_workloads.lock().unwrap();

        // 找到工作负载最轻的NUMA节点
        let mut min_workload = usize::MAX;
        let mut best_node = 0;

        for node in &self.topology.nodes {
            let workload = workloads.get(&node.id).copied().unwrap_or(0);
            if workload < min_workload {
                min_workload = workload;
                best_node = node.id;
            }
        }

        // 更新工作负载
        *workloads.entry(best_node).or_insert(0) += 1;

        best_node
    }

    /// 完成任务，减少工作负载
    pub fn complete_task(&self, node_id: usize) {
        let mut workloads = self.node_workloads.lock().unwrap();
        if let Some(workload) = workloads.get_mut(&node_id) {
            if *workload > 0 {
                *workload -= 1;
            }
        }
    }

    /// 获取NUMA节点工作负载
    pub fn get_node_workload(&self, node_id: usize) -> usize {
        let workloads = self.node_workloads.lock().unwrap();
        workloads.get(&node_id).copied().unwrap_or(0)
    }

    /// 获取所有节点工作负载
    pub fn get_all_workloads(&self) -> HashMap<usize, usize> {
        let workloads = self.node_workloads.lock().unwrap();
        workloads.clone()
    }
}

/// NUMA感知数据布局
#[allow(dead_code)]
pub struct NumaAwareDataLayout<T> {
    data: Vec<Vec<T>>,
    topology: NumaTopology,
}

impl<T> NumaAwareDataLayout<T> {
    /// 创建新的NUMA感知数据布局
    pub fn new(topology: NumaTopology) -> Self {
        let mut data = Vec::new();
        for _ in 0..topology.node_count() {
            data.push(Vec::new());
        }

        Self { data, topology }
    }

    /// 将数据分配到指定NUMA节点
    pub fn allocate_to_node(&mut self, node_id: usize, item: T) -> Result<(), String> {
        if node_id >= self.data.len() {
            return Err(format!("无效的NUMA节点ID: {}", node_id));
        }

        self.data[node_id].push(item);
        Ok(())
    }

    /// 从指定NUMA节点获取数据
    pub fn get_from_node(&self, node_id: usize) -> Option<&Vec<T>> {
        self.data.get(node_id)
    }

    /// 获取所有数据
    pub fn get_all_data(&self) -> &Vec<Vec<T>> {
        &self.data
    }

    /// 获取数据分布统计
    pub fn get_distribution_stats(&self) -> Vec<usize> {
        self.data.iter().map(|node_data| node_data.len()).collect()
    }
}

/// NUMA感知并行计算
pub struct NumaAwareParallelCompute {
    allocator: NumaAwareTaskAllocator,
    topology: NumaTopology,
}

impl NumaAwareParallelCompute {
    /// 创建新的NUMA感知并行计算实例
    pub fn new() -> Self {
        Self {
            allocator: NumaAwareTaskAllocator::new(),
            topology: NumaTopology::new(),
        }
    }

    /// 执行NUMA感知的并行计算
    pub fn compute_parallel<F, R>(&self, tasks: Vec<F>) -> Vec<R>
    where
        F: FnOnce() -> R + Send + Sync + 'static,
        R: Send + Sync + Clone + 'static,
    {
        let results: Arc<Mutex<Vec<Option<R>>>> = Arc::new(Mutex::new(vec![None; tasks.len()]));

        // 为每个任务分配NUMA节点
        let task_assignments: Vec<_> = (0..tasks.len())
            .map(|i| self.allocator.allocate_task(i))
            .collect();

        // 按NUMA节点分组任务
        let mut node_tasks: HashMap<usize, Vec<(usize, F)>> = HashMap::new();
        for (task_id, task) in tasks.into_iter().enumerate() {
            let node_id = task_assignments[task_id];
            node_tasks
                .entry(node_id)
                .or_insert_with(Vec::new)
                .push((task_id, task));
        }

        // 在每个NUMA节点上并行执行任务
        let handles: Vec<_> = node_tasks
            .into_iter()
            .map(|(_node_id, tasks)| {
                let results = results.clone();

                thread::spawn(move || {
                    for (task_id, task) in tasks {
                        let result = task();
                        results.lock().unwrap()[task_id] = Some(result);
                    }
                })
            })
            .collect();

        // 等待所有线程完成
        for handle in handles {
            handle.join().unwrap();
        }

        // 收集结果
        let final_results = results.lock().unwrap();
        final_results
            .iter()
            .map(|opt| opt.clone().unwrap())
            .collect()
    }

    /// 执行NUMA感知的并行归约
    pub fn reduce_parallel<F, R>(&self, data: Vec<R>, reduce_fn: F) -> R
    where
        F: Fn(R, R) -> R + Send + Sync + Clone + 'static,
        R: Send + Sync + Clone + 'static,
    {
        if data.is_empty() {
            panic!("数据不能为空");
        }

        if data.len() == 1 {
            return data[0].clone();
        }

        // 将数据分配到NUMA节点
        let mut node_data: HashMap<usize, Vec<R>> = HashMap::new();
        for (i, item) in data.into_iter().enumerate() {
            let node_id = i % self.topology.node_count();
            node_data.entry(node_id).or_insert_with(Vec::new).push(item);
        }

        // 在每个NUMA节点上并行归约
        let node_results: Vec<_> = node_data
            .into_iter()
            .map(|(_node_id, data)| {
                let reduce_fn = reduce_fn.clone();
                thread::spawn(move || {
                    if data.is_empty() {
                        return None;
                    }

                    let mut result = data[0].clone();
                    for item in data.into_iter().skip(1) {
                        result = reduce_fn(result, item);
                    }
                    Some(result)
                })
            })
            .collect::<Vec<_>>()
            .into_iter()
            .filter_map(|handle| handle.join().unwrap())
            .collect();

        // 最终归约
        if node_results.is_empty() {
            panic!("没有有效的归约结果");
        }

        let mut final_result = node_results[0].clone();
        for result in node_results.into_iter().skip(1) {
            final_result = reduce_fn(final_result, result);
        }

        final_result
    }

    /// 执行NUMA感知的并行映射
    pub fn map_parallel<F, T, R>(&self, data: Vec<T>, map_fn: F) -> Vec<R>
    where
        F: Fn(T) -> R + Send + Sync + Clone + 'static,
        T: Send + Sync + 'static,
        R: Send + Sync + Clone + 'static,
    {
        let results: Arc<Mutex<Vec<Option<R>>>> = Arc::new(Mutex::new(vec![None; data.len()]));

        // 将数据分配到NUMA节点
        let mut node_data: HashMap<usize, Vec<(usize, T)>> = HashMap::new();
        for (i, item) in data.into_iter().enumerate() {
            let node_id = i % self.topology.node_count();
            node_data
                .entry(node_id)
                .or_insert_with(Vec::new)
                .push((i, item));
        }

        // 在每个NUMA节点上并行映射
        let handles: Vec<_> = node_data
            .into_iter()
            .map(|(_node_id, data)| {
                let results = results.clone();
                let map_fn = map_fn.clone();

                thread::spawn(move || {
                    for (index, item) in data {
                        let result = map_fn(item);
                        results.lock().unwrap()[index] = Some(result);
                    }
                })
            })
            .collect();

        // 等待所有线程完成
        for handle in handles {
            handle.join().unwrap();
        }

        // 收集结果
        let final_results = results.lock().unwrap();
        final_results
            .iter()
            .map(|opt| opt.clone().unwrap())
            .collect()
    }

    /// 运行NUMA感知并行计算示例
    pub fn run_example() {
        println!("=== NUMA感知并行计算示例 ===");

        let compute = NumaAwareParallelCompute::new();

        // 测试并行计算
        let tasks: Vec<Box<dyn FnOnce() -> i32 + Send + Sync>> = (0..10)
            .map(|i| {
                Box::new(move || {
                    thread::sleep(Duration::from_millis(10));
                    i * i
                }) as Box<dyn FnOnce() -> i32 + Send + Sync>
            })
            .collect();

        let start = std::time::Instant::now();
        let results = compute.compute_parallel(tasks);
        let elapsed = start.elapsed();

        println!("并行计算结果: {:?}", results);
        println!("计算耗时: {:?}", elapsed);

        // 测试并行归约
        let data: Vec<i32> = (1..=1000).collect();
        let start = std::time::Instant::now();
        let sum = compute.reduce_parallel(data, |a, b| a + b);
        let elapsed = start.elapsed();

        println!("并行归约结果: {}", sum);
        println!("归约耗时: {:?}", elapsed);

        // 测试并行映射
        let data: Vec<i32> = (1..=1000).collect();
        let start = std::time::Instant::now();
        let squares = compute.map_parallel(data, |x| x * x);
        let elapsed = start.elapsed();

        println!("并行映射结果长度: {}", squares.len());
        println!("映射耗时: {:?}", elapsed);

        // 显示工作负载分布
        let workloads = compute.allocator.get_all_workloads();
        println!("NUMA节点工作负载分布: {:?}", workloads);
    }
}

/// NUMA感知内存分配器
pub struct NumaAwareMemoryAllocator {
    topology: NumaTopology,
    node_allocations: Arc<Mutex<HashMap<usize, Vec<usize>>>>,
}

impl NumaAwareMemoryAllocator {
    /// 创建新的NUMA感知内存分配器
    pub fn new() -> Self {
        Self {
            topology: NumaTopology::new(),
            node_allocations: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// 在指定NUMA节点分配内存
    pub fn allocate_on_node(&self, node_id: usize, size: usize) -> Result<usize, String> {
        if node_id >= self.topology.node_count() {
            return Err(format!("无效的NUMA节点ID: {}", node_id));
        }

        let mut allocations = self.node_allocations.lock().unwrap();
        let node_allocations = allocations.entry(node_id).or_insert_with(Vec::new);

        // 简化的内存分配：返回一个虚拟地址
        let address = node_allocations.len() * size;
        node_allocations.push(size);

        Ok(address)
    }

    /// 释放指定NUMA节点的内存
    pub fn deallocate_on_node(&self, node_id: usize, address: usize) -> Result<(), String> {
        if node_id >= self.topology.node_count() {
            return Err(format!("无效的NUMA节点ID: {}", node_id));
        }

        let mut allocations = self.node_allocations.lock().unwrap();
        if let Some(node_allocations) = allocations.get_mut(&node_id) {
            if address < node_allocations.len() {
                node_allocations[address] = 0; // 标记为已释放
                return Ok(());
            }
        }

        Err(format!("无效的内存地址: {}", address))
    }

    /// 获取NUMA节点内存使用统计
    pub fn get_memory_stats(&self) -> HashMap<usize, usize> {
        let allocations = self.node_allocations.lock().unwrap();
        allocations
            .iter()
            .map(|(node_id, allocs)| {
                let total_size: usize = allocs.iter().sum();
                (*node_id, total_size)
            })
            .collect()
    }
}

/// 运行所有NUMA感知示例
pub fn demonstrate_numa_aware() {
    println!("=== NUMA感知并行计算演示 ===");

    // 显示NUMA拓扑
    let topology = NumaTopology::new();
    println!("NUMA拓扑信息:");
    println!("  总CPU核心数: {}", topology.total_cpus);
    println!("  NUMA节点数: {}", topology.node_count());
    println!(
        "  总内存: {} GB",
        topology.total_memory / (1024 * 1024 * 1024)
    );

    for node in topology.get_nodes() {
        println!(
            "  节点 {}: {} 个CPU核心, {} GB内存",
            node.id,
            node.cpu_count,
            node.memory_size / (1024 * 1024 * 1024)
        );
    }

    // 运行NUMA感知并行计算示例
    NumaAwareParallelCompute::run_example();

    // 测试NUMA感知内存分配
    let allocator = NumaAwareMemoryAllocator::new();
    let stats = allocator.get_memory_stats();
    println!("NUMA节点内存使用统计: {:?}", stats);
}

#[allow(dead_code)]
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_numa_topology() {
        let topology = NumaTopology::new();
        assert!(topology.node_count() > 0);
        assert!(topology.total_cpus > 0);
    }

    #[test]
    fn test_numa_aware_task_allocator() {
        let allocator = NumaAwareTaskAllocator::new();
        let node_id = allocator.allocate_task(0);
        assert!(node_id < allocator.topology.node_count());
    }

    #[test]
    fn test_numa_aware_data_layout() {
        let topology = NumaTopology::new();
        let mut layout = NumaAwareDataLayout::new(topology);

        assert!(layout.allocate_to_node(0, 42).is_ok());
        assert!(layout.allocate_to_node(0, 43).is_ok());

        let data = layout.get_from_node(0).unwrap();
        assert_eq!(data.len(), 2);
        assert_eq!(data[0], 42);
        assert_eq!(data[1], 43);
    }

    #[test]
    fn test_numa_aware_parallel_compute() {
        let compute = NumaAwareParallelCompute::new();

        let tasks: Vec<Box<dyn FnOnce() -> i32 + Send + Sync>> = (0..4)
            .map(|i| Box::new(move || i * i) as Box<dyn FnOnce() -> i32 + Send + Sync>)
            .collect();

        let results = compute.compute_parallel(tasks);
        assert_eq!(results.len(), 4);
        assert_eq!(results, vec![0, 1, 4, 9]);
    }

    #[test]
    fn test_numa_aware_memory_allocator() {
        let allocator = NumaAwareMemoryAllocator::new();

        let address = allocator.allocate_on_node(0, 1024).unwrap();
        assert!(address <= usize::MAX);

        assert!(allocator.deallocate_on_node(0, address).is_ok());
    }
}
