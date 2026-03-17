use std::sync::{Arc, Mutex, mpsc};
use std::thread;

#[allow(unused)]
#[derive(Clone)]
struct ProducerConsumer<T> {
    sender: mpsc::Sender<T>,
    receiver: Arc<Mutex<mpsc::Receiver<T>>>,
}

#[allow(unused)]
impl<T> ProducerConsumer<T> {
    fn new() -> Self {
        let (sender, receiver) = mpsc::channel();
        ProducerConsumer {
            sender,
            receiver: Arc::new(Mutex::new(receiver)),
        }
    }

    fn produce(&self, item: T) {
        self.sender.send(item).expect("发送生产者消费者消息失败");
    }

    fn consume(&self) -> Option<T> {
        let receiver = self.receiver.lock().expect("生产者-消费者接收器锁被污染");
        receiver.recv().ok()
    }
}

#[allow(unused)]
fn producer_consumer() {
    let pc = ProducerConsumer::new();

    let producer = {
        let pc = pc.clone();
        thread::spawn(move || {
            for i in 0..10 {
                pc.produce(i);
                println!("Produced: {}", i);
            }
        })
    };

    let consumer = {
        let pc = pc.clone();
        thread::spawn(move || {
            for _ in 0..10 {
                if let Some(item) = pc.consume() {
                    println!("Consumed: {}", item);
                }
            }
        })
    };

    producer.join().expect("生产者线程加入失败");
    consumer.join().expect("消费者线程加入失败");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_producer_consumer01() {
        producer_consumer();
    }
}
