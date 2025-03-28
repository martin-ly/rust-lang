use tokio::sync::mpsc;
use tokio::time::{sleep, Duration};

#[allow(unused)]
#[derive(Debug)]
enum Event {
    UserInput(String),
    TimerTick,
}

async fn event_handler(mut rx: mpsc::Receiver<Event>) {
    while let Some(event) = rx.recv().await {
        match event {
            Event::UserInput(input) => {
                println!("处理用户输入: {}", input);
            }
            Event::TimerTick => {
                println!("处理定时器滴答事件");
            }
        }
    }
}

async fn user_input(tx: mpsc::Sender<Event>) {
    let inputs = vec!["事件1".to_string(), "事件2".to_string(), "事件3".to_string()];

    for input in inputs {
        tx.send(Event::UserInput(input)).await.unwrap();
        sleep(Duration::from_secs(1)).await; // 模拟用户输入延迟
    }
}

async fn timer(tx: mpsc::Sender<Event>) {
    for _ in 0..5 {
        sleep(Duration::from_secs(1)).await; // 模拟定时器间隔
        tx.send(Event::TimerTick).await.unwrap();
    }
}

#[allow(unused)]
async fn event_driven() {
    let (tx, rx) = mpsc::channel(10);

    let handler = tokio::spawn(event_handler(rx));
    let input = tokio::spawn(user_input(tx.clone()));
    let timer_task = tokio::spawn(timer(tx));

    // 等待所有任务完成
    let _ = tokio::join!(handler, input, timer_task);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_event_driven01() {
        event_driven().await;
    }
}

