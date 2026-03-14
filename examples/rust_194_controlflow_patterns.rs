//! Rust 1.94 `ControlFlow` 深度示例
//!
//! 本文件演示 `std::ops::ControlFlow` 在实际生产场景中的高级应用，
//! 包括流控制、错误处理和提前终止模式。

use std::ops::ControlFlow;

/// 连接池健康检查
/// 
/// 使用 ControlFlow 快速检查是否有可用连接，
/// 找到第一个可用连接即停止迭代。
pub struct ConnectionPool {
    connections: Vec<Connection>,
}

#[derive(Debug, Clone)]
pub struct Connection {
    id: u64,
    available: bool,
    last_ping_ms: u64,
}

impl ConnectionPool {
    pub fn new(connections: Vec<Connection>) -> Self {
        Self { connections }
    }
    
    /// 快速检查是否有可用连接
    /// 
    /// 性能优势：找到第一个可用连接即停止，避免遍历整个列表
    pub fn has_available(&self) -> bool {
        matches!(
            self.connections.iter().try_fold(
                ControlFlow::Continue(()),
                |_, conn| {
                    if conn.is_available() {
                        ControlFlow::Break(true)
                    } else {
                        ControlFlow::Continue(())
                    }
                }
            ),
            ControlFlow::Break(true)
        )
    }
    
    /// 查找第一个可用连接
    pub fn find_first_available(&self) -> Option<&Connection> {
        match self.connections.iter().try_fold(
            ControlFlow::Continue(None),
            |_, conn| {
                if conn.is_available() {
                    ControlFlow::Break(Some(conn))
                } else {
                    ControlFlow::Continue(None)
                }
            }
        ) {
            ControlFlow::Break(conn) => conn,
            ControlFlow::Continue(_) => None,
        }
    }
    
    /// 批量验证连接，返回第一个失效的连接
    pub fn find_first_invalid(&self) -> Option<&Connection> {
        match self.connections.iter().try_fold(
            ControlFlow::Continue(()),
            |_, conn| {
                if conn.is_valid() {
                    ControlFlow::Continue(())
                } else {
                    ControlFlow::Break(Some(conn))
                }
            }
        ) {
            ControlFlow::Break(conn) => conn,
            _ => None,
        }
    }
}

impl Connection {
    pub fn new(id: u64, available: bool, last_ping_ms: u64) -> Self {
        Self { id, available, last_ping_ms }
    }
    
    fn is_available(&self) -> bool {
        self.available && self.last_ping_ms < 1000
    }
    
    fn is_valid(&self) -> bool {
        self.last_ping_ms < 5000
    }
}

/// 批处理控制器
/// 
/// 使用 ControlFlow 实现复杂的批处理边界控制，
/// 支持超时、错误阈值和提前终止。
pub struct BatchProcessor<T> {
    items: Vec<T>,
    config: BatchConfig,
}

#[derive(Debug, Clone)]
pub struct BatchConfig {
    pub error_threshold: usize,
    pub max_duration_ms: u64,
}

#[derive(Debug)]
pub struct BatchResult<T> {
    pub processed: Vec<T>,
    pub failed: Vec<(T, String)>,
    pub reason: CompletionReason,
}

#[derive(Debug)]
pub enum CompletionReason {
    AllSucceeded,
    ErrorThresholdReached { threshold: usize, actual: usize },
    TimeoutReached { elapsed_ms: u64 },
}

impl<T: Clone> BatchProcessor<T> {
    pub fn new(items: Vec<T>, config: BatchConfig) -> Self {
        Self { items, config }
    }
    
    /// 处理批次，使用 ControlFlow 控制流程
    pub async fn process<F, Fut>(&self, mut processor: F) -> BatchResult<T>
    where
        F: FnMut(&T) -> Fut,
        Fut: std::future::Future<Output = Result<T, String>>,
    {
        let mut processed = Vec::new();
        let mut failed = Vec::new();
        let start = std::time::Instant::now();
        
        for item in &self.items {
            // 检查超时
            let elapsed = start.elapsed().as_millis() as u64;
            if elapsed >= self.config.max_duration_ms {
                return BatchResult {
                    processed,
                    failed,
                    reason: CompletionReason::TimeoutReached { elapsed_ms: elapsed },
                };
            }
            
            match processor(item).await {
                Ok(result) => processed.push(result),
                Err(e) => {
                    failed.push((item.clone(), e));
                    if failed.len() >= self.config.error_threshold {
                        return BatchResult {
                            processed,
                            failed,
                            reason: CompletionReason::ErrorThresholdReached {
                                threshold: self.config.error_threshold,
                                actual: failed.len(),
                            },
                        };
                    }
                }
            }
        }
        
        BatchResult {
            processed,
            failed,
            reason: CompletionReason::AllSucceeded,
        }
    }
}

/// 树形结构搜索
/// 
/// 使用 ControlFlow 实现深度优先搜索，找到目标即停止。
#[derive(Debug)]
pub struct TreeNode<T> {
    pub value: T,
    pub children: Vec<TreeNode<T>>,
}

impl<T: PartialEq + Clone> TreeNode<T> {
    /// 深度优先搜索，找到目标值即停止
    pub fn dfs_find(&self, target: &T) -> Option<T> {
        match self.dfs_recursive(target) {
            ControlFlow::Break(found) => Some(found),
            ControlFlow::Continue(_) => None,
        }
    }
    
    fn dfs_recursive(&self, target: &T) -> ControlFlow<T, ()> {
        if &self.value == target {
            return ControlFlow::Break(self.value.clone());
        }
        
        for child in &self.children {
            match child.dfs_recursive(target) {
                ControlFlow::Break(found) => return ControlFlow::Break(found),
                ControlFlow::Continue(_) => continue,
            }
        }
        
        ControlFlow::Continue(())
    }
}

/// 管道处理模式
/// 
/// 使用 ControlFlow 构建可组合的处理管道。
pub struct ProcessingPipeline<T, E> {
    steps: Vec<Box<dyn Fn(T) -> ControlFlow<E, T>>>,
}

impl<T, E> ProcessingPipeline<T, E> {
    pub fn new() -> Self {
        Self { steps: Vec::new() }
    }
    
    pub fn add<F>(mut self, step: F) -> Self
    where
        F: Fn(T) -> ControlFlow<E, T> + 'static,
    {
        self.steps.push(Box::new(step));
        self
    }
    
    pub fn execute(&self, input: T) -> ControlFlow<E, T> {
        let mut current = input;
        for step in &self.steps {
            match step(current) {
                ControlFlow::Continue(val) => current = val,
                ControlFlow::Break(err) => return ControlFlow::Break(err),
            }
        }
        ControlFlow::Continue(current)
    }
}

/// 错误累积与报告
/// 
/// 使用 ControlFlow 收集所有错误后再统一处理。
pub fn validate_all<T, E>(
    items: Vec<T>,
    validator: impl Fn(&T) -> Result<(), E>,
) -> ControlFlow<Vec<E>, Vec<T>> {
    let mut errors = Vec::new();
    
    for item in &items {
        if let Err(e) = validator(item) {
            errors.push(e);
        }
    }
    
    if errors.is_empty() {
        ControlFlow::Continue(items)
    } else {
        ControlFlow::Break(errors)
    }
}

/// 分页数据获取
/// 
/// 使用 ControlFlow 控制分页获取，直到满足条件或数据耗尽。
pub async fn fetch_paginated_data<F, Fut, T>(
    mut fetch_page: F,
    max_items: usize,
) -> Vec<T>
where
    F: FnMut(usize) -> Fut,
    Fut: std::future::Future<Output = Option<Vec<T>>>,
{
    let mut all_data = Vec::new();
    let mut page = 0;
    
    loop {
        match fetch_page(page).await {
            Some(items) => {
                for item in items {
                    if all_data.len() >= max_items {
                        return all_data;
                    }
                    all_data.push(item);
                }
                page += 1;
            }
            None => break,
        }
    }
    
    all_data
}

#[tokio::main]
async fn main() {
    println!("=== Rust 1.94 ControlFlow 深度示例 ===\n");
    
    // 1. 连接池示例
    let connections = vec![
        Connection::new(1, false, 2000),  // 不可用
        Connection::new(2, true, 500),     // 可用
        Connection::new(3, true, 800),     // 可用
    ];
    let pool = ConnectionPool::new(connections);
    
    println!("有可用连接: {}", pool.has_available());
    println!("第一个可用: {:?}\n", pool.find_first_available());
    
    // 2. 树搜索示例
    let tree = TreeNode {
        value: 1,
        children: vec![
            TreeNode {
                value: 2,
                children: vec![
                    TreeNode { value: 4, children: vec![] },
                    TreeNode { value: 5, children: vec![] },
                ],
            },
            TreeNode {
                value: 3,
                children: vec![
                    TreeNode { value: 6, children: vec![] },
                    TreeNode { value: 7, children: vec![] },
                ],
            },
        ],
    };
    
    println!("查找 5: {:?}", tree.dfs_find(&5));
    println!("查找 10: {:?}\n", tree.dfs_find(&10));
    
    // 3. 管道示例
    let pipeline = ProcessingPipeline::new()
        .add(|x: i32| {
            if x > 0 { ControlFlow::Continue(x * 2) } 
            else { ControlFlow::Break("负数错误") }
        })
        .add(|x| ControlFlow::Continue(x + 10))
        .add(|x| {
            if x < 100 { ControlFlow::Continue(x) }
            else { ControlFlow::Break("超出范围") }
        });
    
    println!("管道 5: {:?}", pipeline.execute(5));
    println!("管道 -5: {:?}", pipeline.execute(-5));
    println!("管道 50: {:?}\n", pipeline.execute(50));
    
    println!("所有示例完成！");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_connection_pool() {
        let connections = vec![
            Connection::new(1, false, 2000),
            Connection::new(2, true, 500),
        ];
        let pool = ConnectionPool::new(connections);
        
        assert!(pool.has_available());
        assert_eq!(pool.find_first_available().unwrap().id, 2);
    }
    
    #[test]
    fn test_tree_search() {
        let tree = TreeNode {
            value: 1,
            children: vec![TreeNode { value: 2, children: vec![] }],
        };
        
        assert_eq!(tree.dfs_find(&2), Some(2));
        assert_eq!(tree.dfs_find(&3), None);
    }
    
    #[test]
    fn test_pipeline() {
        let pipeline = ProcessingPipeline::new()
            .add(|x: i32| ControlFlow::Continue(x * 2));
        
        assert_eq!(pipeline.execute(5), ControlFlow::Continue(10));
    }
}
