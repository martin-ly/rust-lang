//! 递归异步与结构化并发示例（Rust 1.90）
//! - 显式栈的迭代 DFS（避免自引用 async 递归）
//! - 带并发上限与取消的分治任务

use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{mpsc, Semaphore};
use tokio::task::JoinSet;

#[allow(dead_code)]
#[derive(Clone, Debug)]
struct Node {
    id: usize,
    children: Vec<usize>,
}

fn sample_tree() -> Vec<Node> {
    vec![
        Node { id: 0, children: vec![1, 2] },
        Node { id: 1, children: vec![3, 4] },
        Node { id: 2, children: vec![5] },
        Node { id: 3, children: vec![] },
        Node { id: 4, children: vec![] },
        Node { id: 5, children: vec![] },
    ]
}

// 显式栈的“递归”遍历，避免 async 自引用
async fn iterative_dfs_sum(tree: &[Node], root: usize) -> usize {
    let mut stack = vec![root];
    let mut sum = 0usize;
    while let Some(n) = stack.pop() {
        sum += n;
        if let Some(node) = tree.get(n) {
            for &c in &node.children {
                stack.push(c);
            }
        }
        // 模拟异步点
        tokio::task::yield_now().await;
    }
    sum
}

// 带并发上限/背压的分治处理示例
async fn bounded_parallel_process(tree: Vec<Node>, root: usize) -> usize {
    let semaphore = Arc::new(Semaphore::new(3)); // 并发上限
    let (tx, mut rx) = mpsc::channel::<usize>(8); // 有界通道作为背压

    let mut set = JoinSet::new();
    let tx_root = tx.clone();
    set.spawn(async move {
        let _ = tx_root.send(root).await;
    });

    let mut total = 0usize;

    while let Some(Ok(_task)) = set.join_next().await {
        // 回收已完成任务（如有）
        // 拉取待处理节点，受通道容量限制
        while let Some(n) = tokio::time::timeout(Duration::from_millis(5), rx.recv())
            .await
            .ok()
            .flatten()
        {
            total += n; // 模拟聚合

            if let Some(node) = tree.get(n).cloned() {
                for c in node.children {
                    let permit = semaphore.clone().acquire_owned().await.unwrap();
                    let tx_cloned = tx.clone();
                    set.spawn(async move {
                        // 模拟 I/O 或计算
                        tokio::time::sleep(Duration::from_millis(10)).await;
                        let _p = permit; // 释放即降低并发
                        let _ = tx_cloned.send(c).await; // 若队列满则背压
                    });
                }
            }
        }
        // 无任务到达，短暂让出
        tokio::task::yield_now().await;
        if set.is_empty() && rx.is_closed() {
            break;
        }
        // 退出条件：示例中由 JoinSet 清空 + 通道耗尽隐式达成
    }

    total
}

#[tokio::main]
async fn main() {
    let tree = sample_tree();

    // 1) 迭代 DFS，避免递归 async 自引用
    let sum = iterative_dfs_sum(&tree, 0).await;
    println!("iterative_dfs_sum={}", sum);

    // 2) 分治并发 + 背压 + 限流
    //    外围可再包一层 timeout/cancellation 形成结构化并发边界
    let result = tokio::time::timeout(Duration::from_secs(2), bounded_parallel_process(tree, 0))
        .await
        .expect("timeout")
        ;
    println!("bounded_parallel_process_total={}", result);
}


