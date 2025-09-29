use std::time::Duration;

use tokio::select;
use tokio::sync::mpsc;
use tokio::time::sleep;
use tracing::{info, warn};

#[derive(Clone, Debug)]
enum Priority {
    High,
    Normal,
}

#[derive(Clone, Debug)]
struct Message {
    priority: Priority,
    payload: String,
}

/// 简化的 Actor：仅负责接收消息并按优先级路由到内部 CSP 流水线入口
#[derive(Clone)]
struct IngressActor {
    tx_high: mpsc::Sender<Message>,
    tx_norm: mpsc::Sender<Message>,
}

impl IngressActor {
    fn new(tx_high: mpsc::Sender<Message>, tx_norm: mpsc::Sender<Message>) -> Self {
        Self { tx_high, tx_norm }
    }

    async fn send(&self, msg: Message) {
        let res = match msg.priority {
            Priority::High => self.tx_high.send(msg).await,
            Priority::Normal => self.tx_norm.send(msg).await,
        };
        if let Err(e) = res {
            warn!(error = %e, "ingress mailbox full or closed");
        }
    }
}

/// 将两个优先级邮箱合并为一个 CSP 入口，使用 select 抢占高优先级
async fn run_mailbox_mux(
    mut rx_high: mpsc::Receiver<Message>,
    mut rx_norm: mpsc::Receiver<Message>,
    tx_pipeline: mpsc::Sender<Message>,
) {
    loop {
        select! {
            biased;
            Some(msg) = rx_high.recv() => {
                // 高优先级先处理
                if tx_pipeline.send(msg).await.is_err() {
                    warn!("pipeline closed");
                    break;
                }
            }
            Some(msg) = rx_norm.recv() => {
                if tx_pipeline.send(msg).await.is_err() {
                    warn!("pipeline closed");
                    break;
                }
            }
            else => {
                // 两个邮箱均已关闭
                break;
            }
        }
    }
}

/// 简单的流水线阶段：模拟处理耗时，并打印 trace
async fn run_pipeline_stage(mut rx: mpsc::Receiver<Message>) {
    while let Some(msg) = rx.recv().await {
        match msg.priority {
            Priority::High => info!(payload=%msg.payload, "stage: HIGH"),
            Priority::Normal => info!(payload=%msg.payload, "stage: NORM"),
        }
        // 模拟 I/O 或计算耗时
        sleep(Duration::from_millis(30)).await;
    }
}

#[tokio::main]
async fn main() {
    // 初始化 tracing（最简）
    let _ = tracing_subscriber::fmt()
        .with_env_filter("info")
        .with_target(false)
        .try_init();

    // 1) 优先级邮箱（Actor 侧）
    let (tx_high, rx_high) = mpsc::channel::<Message>(16);
    let (tx_norm, rx_norm) = mpsc::channel::<Message>(64);

    let ingress = IngressActor::new(tx_high.clone(), tx_norm.clone());

    // 2) CSP 流水线入口
    let (tx_pipeline, rx_pipeline) = mpsc::channel::<Message>(64);

    // 3) 启动合并器（优先级邮箱 → CSP 入口）
    let mux_handle = tokio::spawn(run_mailbox_mux(rx_high, rx_norm, tx_pipeline.clone()));

    // 4) 启动一个简单的流水线阶段
    let stage_handle = tokio::spawn(run_pipeline_stage(rx_pipeline));

    // 5) 发送若干消息（混合优先级）
    for i in 0..10 {
        ingress
            .send(Message {
                priority: if i % 3 == 0 { Priority::High } else { Priority::Normal },
                payload: format!("msg-{i}"),
            })
            .await;
    }

    // 稍等一会让处理完成
    sleep(Duration::from_millis(800)).await;

    drop(tx_high);
    drop(tx_norm);
    drop(tx_pipeline);

    let _ = mux_handle.await;
    let _ = stage_handle.await;
}


