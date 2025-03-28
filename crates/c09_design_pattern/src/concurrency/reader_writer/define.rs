use std::sync::{Arc, RwLock};
use std::thread;
use std::time::Duration;

#[allow(unused)]
struct SharedData<T> {
    data: RwLock<T>,
}

#[allow(unused)]
impl<T> SharedData<T> {
    fn new(data: T) -> Self {
        SharedData {
            data: RwLock::new(data),
        }
    }

    fn read_data(&self) -> T
    where
        T: Copy,
    {
        let read_guard = self.data.read().unwrap();
        *read_guard
    }

    fn write_data(&self, new_data: T) {
        let mut write_guard = self.data.write().unwrap();
        *write_guard = new_data;
    }
}

#[allow(unused)]
fn reader_writer() {
    let shared_data = Arc::new(SharedData::new(0));

    let writers: Vec<_> = (0..3)
    .map(|i| {
        let shared_data = Arc::clone(&shared_data);
        thread::spawn(move || {
            // loop {
                shared_data.write_data(i);
                println!("Writer wrote: {}", i);
                thread::sleep(Duration::from_millis(100));
            // }
        })
    })
    .collect();

    let readers: Vec<_> = (0..3)
        .map(|_| {
            let shared_data = Arc::clone(&shared_data);
            thread::spawn(move || {
                // loop {
                    let data = shared_data.read_data();
                    println!("Reader read: {}", data);
                    thread::sleep(Duration::from_millis(100));
                // }
            })
        })
        .collect();



    for reader in readers {
        reader.join().unwrap();
    }

    for writer in writers {
        writer.join().unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reader_writer01() {
        reader_writer();
    }
}

