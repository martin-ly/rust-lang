use tokio::sync::mpsc;
use tokio::time::{sleep, Duration};
use tokio::signal;

#[allow(unused)]
#[derive(Debug)]
struct Subject {
    observers: Vec<mpsc::Sender<String>>,
}

#[allow(unused)]
impl Subject {
    fn new() -> Self {
        Subject {
            observers: Vec::new(),
        }
    }

    fn attach(&mut self, observer: mpsc::Sender<String>) {
        self.observers.push(observer);
    }

    async fn notify(&self, message: String) {
        for observer in &self.observers {
            let _ = observer.send(message.clone()).await; // 发送通知
        }
    }

    async fn change_state(&self, new_state: &str) {
        println!("状态改变: {}", new_state);
        self.notify(new_state.to_string()).await; // 通知所有观察者
    }
}

#[allow(unused)]
async fn observer(id: u32, mut rx: mpsc::Receiver<String>) {
    while let Some(message) = rx.recv().await {
        println!("观察者 {} 收到通知: {}", id, message);
    }
}

#[allow(unused)]
async fn observer_pattern() {
    // 监听 Ctrl+C 信号
    let signal_handle = tokio::spawn(async {
        signal::ctrl_c().await.expect("无法监听 Ctrl+C");
        println!("监听到Ctrl+C信号,退出程序...");
    });

    let (tx1, rx1) = mpsc::channel(10);
    let (tx2, rx2) = mpsc::channel(10);

    let mut subject = Subject::new();
    subject.attach(tx1);
    subject.attach(tx2);

    // 启动观察者
    let observer1 = tokio::spawn(observer(1, rx1));
    let observer2 = tokio::spawn(observer(2, rx2));

    // 模拟状态变化
    subject.change_state("状态1").await;
    sleep(Duration::from_secs(1)).await;
    subject.change_state("状态2").await;



    // 等待观察者完成
    let _ = tokio::join!(observer1, observer2, signal_handle);
    println!("主线程退出。");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_observer_pattern01() {
        observer_pattern().await;
    }
}

