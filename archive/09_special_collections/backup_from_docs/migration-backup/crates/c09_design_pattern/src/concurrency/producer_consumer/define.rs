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
        self.sender.send(item).unwrap();
    }

    fn consume(&self) -> Option<T> {
        let receiver = self.receiver.lock().unwrap();
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

    producer.join().unwrap();
    consumer.join().unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_producer_consumer01() {
        producer_consumer();
    }
}
