use std::sync::{Arc, Mutex};
use std::thread;

#[allow(unused)]
#[derive(Clone)]
struct SharedState<T> {
    data: Arc<Mutex<T>>,
}

impl<T> SharedState<T> {
    fn new(data: T) -> Self {
        SharedState {
            data: Arc::new(Mutex::new(data)),
        }
    }

    fn update<F>(&self, update_fn: F)
    where
        F: FnOnce(&mut T),
    {
        let mut data = self.data.lock().unwrap();
        update_fn(&mut data);
    }

    fn get(&self) -> T
    where
        T: Copy,
    {
        let data = self.data.lock().unwrap();
        *data
    }
}

#[allow(unused)]
fn shared_state() {
    let shared_state = SharedState::new(0);

    let handles: Vec<_> = (0..10)
        .map(|_| {
            let state_clone = shared_state.clone();
            thread::spawn(move || {
                state_clone.update(|data| {
                    *data += 1;
                });
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Final value: {}", shared_state.get());
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shared_state01() {
        shared_state();
    }
}
