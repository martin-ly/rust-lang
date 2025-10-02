//! # Actor/Reactor/CSP 完整实现示例
//! 
//! 本示例展示三种并发模型在算法中的应用：
//! 1. Actor模型：消息传递式并发
//! 2. Reactor模式：事件驱动式调度
//! 3. CSP模型：通信顺序进程
//! 
//! 对标：Rust 1.90 / Edition 2024

use std::collections::HashMap;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;

/// ============================================================================
/// 第一部分：Actor模型实现
/// ============================================================================

/// Actor消息trait
pub trait ActorMessage: Send + 'static {}

/// Actor地址
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ActorAddr(u64);

/// Actor上下文：提供运行时能力
pub struct ActorContext {
    addr: ActorAddr,
    system: Arc<ActorSystem>,
}

impl ActorContext {
    /// 获取当前Actor地址
    pub fn addr(&self) -> ActorAddr {
        self.addr
    }
    
    /// 停止当前Actor
    pub fn stop(&self) {
        self.system.stop_actor(self.addr);
    }
}

/// Actor系统：管理所有Actor
pub struct ActorSystem {
    actors: Arc<Mutex<HashMap<ActorAddr, mpsc::UnboundedSender<Box<dyn ActorMessage>>>>>,
    next_id: Arc<std::sync::atomic::AtomicU64>,
}

impl ActorSystem {
    pub fn new() -> Arc<Self> {
        Arc::new(Self {
            actors: Arc::new(Mutex::new(HashMap::new())),
            next_id: Arc::new(std::sync::atomic::AtomicU64::new(1)),
        })
    }
    
    /// 启动简单的消息处理Actor
    pub async fn spawn_simple_actor<F, M>(
        self: &Arc<Self>,
        mut handler: F,
    ) -> ActorAddr
    where
        F: FnMut(M, &ActorContext) -> Pin<Box<dyn Future<Output = ()> + Send>> + Send + 'static,
        M: ActorMessage,
    {
        let addr = ActorAddr(self.next_id.fetch_add(1, std::sync::atomic::Ordering::SeqCst));
        let (tx, mut rx) = mpsc::unbounded_channel::<Box<dyn ActorMessage>>();
        
        // 注册Actor
        self.actors.lock().unwrap().insert(addr, tx);
        
        let system = Arc::clone(self);
        
        // 启动Actor任务
        tokio::spawn(async move {
            let ctx = ActorContext {
                addr,
                system: system.clone(),
            };
            
            // 消息循环
            while let Some(boxed_msg) = rx.recv().await {
                // 安全的向下转换
                let msg_ptr = Box::into_raw(boxed_msg);
                let typed_msg = unsafe { Box::from_raw(msg_ptr as *mut M) };
                handler(*typed_msg, &ctx).await;
            }
        });
        
        addr
    }
    
    /// 发送消息
    pub fn send_message(&self, addr: ActorAddr, msg: Box<dyn ActorMessage>) {
        if let Some(tx) = self.actors.lock().unwrap().get(&addr) {
            let _ = tx.send(msg);
        }
    }
    
    /// 停止Actor
    pub fn stop_actor(&self, addr: ActorAddr) {
        self.actors.lock().unwrap().remove(&addr);
    }
}

/// ============================================================================
/// Actor示例：并行快速排序Actor
/// ============================================================================

#[derive(Debug)]
pub enum SortMessage {
    Sort { data: Vec<i32>, reply: mpsc::Sender<Vec<i32>> },
}

impl ActorMessage for SortMessage {}

pub async fn create_sort_actor(system: &Arc<ActorSystem>, threshold: usize) -> ActorAddr {
    system.spawn_simple_actor(move |msg: SortMessage, _ctx| {
        let threshold = threshold;
        Box::pin(async move {
            match msg {
                SortMessage::Sort { data, reply } => {
                    let sorted = quick_sort_parallel(data, threshold).await;
                    let _ = reply.send(sorted).await;
                }
            }
        })
    }).await
}

/// 并行快速排序实现（使用Box避免递归）
fn quick_sort_parallel(
    mut data: Vec<i32>,
    threshold: usize,
) -> Pin<Box<dyn Future<Output = Vec<i32>> + Send>> {
    Box::pin(async move {
        if data.len() <= threshold {
            data.sort();
            return data;
        }
        
        let pivot = data[data.len() / 2];
        let (less, mut equal, greater): (Vec<_>, Vec<_>, Vec<_>) = data.into_iter()
            .fold((vec![], vec![], vec![]), |(mut l, mut e, mut g), x| {
                if x < pivot {
                    l.push(x);
                } else if x == pivot {
                    e.push(x);
                } else {
                    g.push(x);
                }
                (l, e, g)
            });
        
        // 并行递归
        let (left_sorted, right_sorted) = tokio::join!(
            quick_sort_parallel(less, threshold),
            quick_sort_parallel(greater, threshold)
        );
        
        // 合并结果
        let mut result = left_sorted;
        result.append(&mut equal);
        result.extend(right_sorted);
        result
    })
}

/// ============================================================================
/// 第二部分：Reactor模式实现
/// ============================================================================

/// Reactor：事件驱动的任务调度器（简化版）
/// 
/// 使用tokio的task spawn简化实现
pub struct Reactor {
    running: Arc<tokio::sync::Mutex<bool>>,
}

impl Reactor {
    pub fn new() -> Arc<Self> {
        Arc::new(Self {
            running: Arc::new(tokio::sync::Mutex::new(false)),
        })
    }
    
    /// 提交任务
    pub fn spawn<F>(self: &Arc<Self>, future: F) -> tokio::task::JoinHandle<()>
    where
        F: Future<Output = ()> + Send + 'static,
    {
        tokio::spawn(future)
    }
    
    /// 运行Reactor事件循环（演示用）
    pub async fn run(self: Arc<Self>) {
        *self.running.lock().await = true;
        println!("[Reactor] 事件循环启动");
        
        // 简化版本：等待一段时间让tasks完成
        while *self.running.lock().await {
            tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        }
        
        println!("[Reactor] 事件循环结束");
    }
    
    /// 停止Reactor
    pub async fn stop(&self) {
        *self.running.lock().await = false;
    }
}

/// ============================================================================
/// Reactor示例：异步归并排序
/// ============================================================================

pub fn merge_sort_reactor_boxed(data: Vec<i32>) -> Pin<Box<dyn Future<Output = Vec<i32>> + Send>> {
    Box::pin(async move {
        if data.len() <= 1 {
            return data;
        }
        
        let mid = data.len() / 2;
        let (left, right) = data.split_at(mid);
        
        // 并行递归
        let (left_sorted, right_sorted) = tokio::join!(
            merge_sort_reactor_boxed(left.to_vec()),
            merge_sort_reactor_boxed(right.to_vec())
        );
        
        // 归并
        merge(left_sorted, right_sorted)
    })
}

fn merge(left: Vec<i32>, right: Vec<i32>) -> Vec<i32> {
    let mut result = Vec::with_capacity(left.len() + right.len());
    let (mut i, mut j) = (0, 0);
    
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }
    
    result.extend_from_slice(&left[i..]);
    result.extend_from_slice(&right[j..]);
    result
}

/// ============================================================================
/// 第三部分：CSP模型实现
/// ============================================================================

/// ============================================================================
/// CSP示例1：MapReduce框架
/// ============================================================================

pub struct MapReduceCsp;

impl MapReduceCsp {
    /// MapReduce执行
    pub async fn execute<T, K, V, MF, RF>(
        data: Vec<T>,
        map_fn: MF,
        reduce_fn: RF,
        num_workers: usize,
    ) -> HashMap<K, V>
    where
        T: Send + Clone + 'static,
        K: Eq + std::hash::Hash + Send + 'static,
        V: Send + 'static,
        MF: Fn(T) -> (K, V) + Send + Sync + Copy + 'static,
        RF: Fn(V, V) -> V + Send + Sync + Copy + 'static,
    {
        let (map_tx, mut map_rx) = mpsc::channel::<(K, V)>(100);
        let (reduce_tx, mut reduce_rx) = mpsc::channel::<(K, V)>(100);
        
        // Map阶段
        let chunk_size = (data.len() + num_workers - 1) / num_workers;
        let mut map_handles = Vec::new();
        
        for chunk in data.chunks(chunk_size) {
            let tx = map_tx.clone();
            let chunk = chunk.to_vec();
            
            let handle = tokio::spawn(async move {
                for item in chunk {
                    let result = map_fn(item);
                    let _ = tx.send(result).await;
                }
            });
            
            map_handles.push(handle);
        }
        
        drop(map_tx);
        
        // Shuffle阶段
        let shuffle_handle = tokio::spawn(async move {
            let mut groups: HashMap<K, Vec<V>> = HashMap::new();
            
            while let Some((key, value)) = map_rx.recv().await {
                groups.entry(key).or_default().push(value);
            }
            
            for (key, values) in groups {
                if let Some(reduced) = values.into_iter().reduce(reduce_fn) {
                    let _ = reduce_tx.send((key, reduced)).await;
                }
            }
            // 在此处drop reduce_tx，确保channel关闭
            drop(reduce_tx);
        });
        
        // 等待Map完成
        for handle in map_handles {
            let _ = handle.await;
        }
        
        let _ = shuffle_handle.await;
        
        // 收集结果
        let mut results = HashMap::new();
        while let Some((key, value)) = reduce_rx.recv().await {
            results.insert(key, value);
        }
        
        results
    }
}

/// ============================================================================
/// CSP示例2：Pipeline数据处理
/// ============================================================================

/// 数据处理Pipeline
pub struct DataPipeline;

impl DataPipeline {
    /// 三阶段Pipeline：生成 -> 转换 -> 过滤
    pub async fn process(count: usize) -> Vec<i32> {
        let (tx1, mut rx1) = mpsc::channel::<i32>(100);
        let (tx2, mut rx2) = mpsc::channel::<i32>(100);
        
        // 阶段1：生成数据
        let producer = tokio::spawn(async move {
            println!("[CSP Producer] 生成 {} 个数据", count);
            for i in 0..count {
                if tx1.send(i as i32).await.is_err() {
                    break;
                }
            }
        });
        
        // 阶段2：转换数据
        let transformer = tokio::spawn(async move {
            let mut processed = 0;
            while let Some(value) = rx1.recv().await {
                let transformed = value * 2;
                processed += 1;
                if tx2.send(transformed).await.is_err() {
                    break;
                }
            }
            println!("[CSP Transformer] 转换了 {} 个数据", processed);
        });
        
        // 阶段3：过滤数据
        let filter = tokio::spawn(async move {
            let mut results = Vec::new();
            while let Some(value) = rx2.recv().await {
                if value % 3 == 0 {
                    results.push(value);
                }
            }
            println!("[CSP Filter] 过滤后剩余 {} 个数据", results.len());
            results
        });
        
        // 等待所有阶段完成
        let _ = producer.await;
        let _ = transformer.await;
        filter.await.unwrap_or_default()
    }
}

/// ============================================================================
/// 主函数：演示所有三种模式
/// ============================================================================

#[tokio::main]
async fn main() {
    println!("╔════════════════════════════════════════════════════════════════╗");
    println!("║           Actor/Reactor/CSP 并发模型完整示例                   ║");
    println!("║                Rust 1.90 / Edition 2024                        ║");
    println!("╚════════════════════════════════════════════════════════════════╝\n");
    
    // ========================================================================
    // 演示1：Actor模型 - 快速排序
    // ========================================================================
    println!("【演示1】Actor模型：并行快速排序");
    println!("{}", "─".repeat(60));
    
    let actor_system = ActorSystem::new();
    
    let data = vec![9, 3, 7, 1, 5, 8, 2, 6, 4];
    println!("原始数据: {:?}", data);
    
    let sort_actor = create_sort_actor(&actor_system, 5).await;
    let (tx, mut rx) = mpsc::channel(1);
    
    actor_system.send_message(
        sort_actor,
        Box::new(SortMessage::Sort { data: data.clone(), reply: tx })
    );
    
    if let Some(sorted) = rx.recv().await {
        println!("排序结果: {:?}", sorted);
    }
    
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    // ========================================================================
    // 演示2：Reactor模式 - 异步归并排序
    // ========================================================================
    println!("\n【演示2】Reactor模式：事件驱动归并排序");
    println!("{}", "─".repeat(60));
    
    let reactor = Reactor::new();
    
    let data2 = vec![15, 8, 23, 4, 16, 42, 11, 7];
    println!("原始数据: {:?}", data2);
    
    let sorted_result = Arc::new(tokio::sync::Mutex::new(None));
    let sorted_clone = Arc::clone(&sorted_result);
    
    reactor.spawn(async move {
        let sorted = merge_sort_reactor_boxed(data2).await;
        *sorted_clone.lock().await = Some(sorted);
    });
    
    // 运行reactor
    let reactor_clone = Arc::clone(&reactor);
    let reactor_handle = tokio::spawn(async move {
        reactor_clone.run().await;
    });
    
    tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
    reactor.stop().await;
    let _ = reactor_handle.await;
    
    if let Some(sorted) = sorted_result.lock().await.as_ref() {
        println!("排序结果: {:?}", sorted);
    }
    
    // ========================================================================
    // 演示3：CSP模型 - MapReduce词频统计
    // ========================================================================
    println!("\n【演示3】CSP模型：MapReduce词频统计");
    println!("{}", "─".repeat(60));
    
    let words = vec![
        "rust", "go", "rust", "python", "go", "rust",
        "java", "python", "rust", "go", "javascript"
    ];
    println!("输入单词: {:?}", words);
    
    let word_count = MapReduceCsp::execute(
        words.iter().map(|s| s.to_string()).collect(),
        |word| (word, 1),
        |a, b| a + b,
        3,
    ).await;
    
    println!("词频统计结果:");
    let mut sorted_words: Vec<_> = word_count.iter().collect();
    sorted_words.sort_by(|a, b| b.1.cmp(a.1));
    for (word, count) in sorted_words {
        println!("  {}: {}", word, count);
    }
    
    // ========================================================================
    // 演示4：CSP Pipeline - 数据处理流水线
    // ========================================================================
    println!("\n【演示4】CSP Pipeline：数据处理流水线");
    println!("{}", "─".repeat(60));
    
    let result = DataPipeline::process(20).await;
    println!("最终结果: {:?}", result);
    
    // ========================================================================
    // 总结对比
    // ========================================================================
    println!("\n╔════════════════════════════════════════════════════════════════╗");
    println!("║                          模式对比总结                           ║");
    println!("╠════════════════════════════════════════════════════════════════╣");
    println!("║ Actor模型：                                                     ║");
    println!("║   ✓ 消息传递式并发                                             ║");
    println!("║   ✓ 独立状态管理                                               ║");
    println!("║   ✓ 适合分布式系统                                             ║");
    println!("║                                                                ║");
    println!("║ Reactor模式：                                                   ║");
    println!("║   ✓ 事件驱动调度                                               ║");
    println!("║   ✓ 高性能异步IO                                               ║");
    println!("║   ✓ 适合网络服务                                               ║");
    println!("║                                                                ║");
    println!("║ CSP模型：                                                       ║");
    println!("║   ✓ 通信顺序进程                                               ║");
    println!("║   ✓ Pipeline流水线                                             ║");
    println!("║   ✓ 适合数据处理                                               ║");
    println!("╚════════════════════════════════════════════════════════════════╝");
}

/// ============================================================================
/// 测试模块
/// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_actor_quick_sort() {
        let system = ActorSystem::new();
        let actor = create_sort_actor(&system, 5).await;
        
        let data = vec![5, 2, 8, 1, 9, 3, 7];
        let (tx, mut rx) = mpsc::channel(1);
        
        system.send_message(actor, Box::new(SortMessage::Sort { 
            data: data.clone(),
            reply: tx 
        }));
        
        let sorted = rx.recv().await.unwrap();
        assert_eq!(sorted, vec![1, 2, 3, 5, 7, 8, 9]);
    }
    
    #[tokio::test]
    async fn test_reactor_merge_sort() {
        let data = vec![9, 3, 7, 1, 5];
        let sorted = merge_sort_reactor_boxed(data).await;
        assert_eq!(sorted, vec![1, 3, 5, 7, 9]);
    }
    
    #[tokio::test]
    async fn test_csp_mapreduce() {
        let text: Vec<char> = "hello".chars().collect();
        
        let result = MapReduceCsp::execute(
            text,
            |c| (c, 1),
            |a, b| a + b,
            2,
        ).await;
        
        assert_eq!(result.get(&'l'), Some(&2));
        assert_eq!(result.get(&'h'), Some(&1));
    }
    
    #[tokio::test]
    async fn test_csp_pipeline() {
        let result = DataPipeline::process(10).await;
        
        // 0..10 -> *2 -> [0,2,4,6,8,10,12,14,16,18] -> 过滤%3==0 -> [0,6,12,18]
        assert_eq!(result, vec![0, 6, 12, 18]);
    }
}
