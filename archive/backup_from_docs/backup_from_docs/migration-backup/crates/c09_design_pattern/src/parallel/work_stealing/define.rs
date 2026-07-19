use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use std::thread;

struct Worker {
    id: usize,
    task_queue: Arc<Mutex<VecDeque<Box<dyn FnOnce() + Send + 'static>>>>,
}

impl Worker {
    fn new(
        id: usize,
        task_queue: Arc<Mutex<VecDeque<Box<dyn FnOnce() + Send + 'static>>>>,
    ) -> Self {
        Worker { id, task_queue }
    }

    fn work(&self) {
        loop {
            let task = {
                let mut queue = self.task_queue.lock().unwrap();
                queue.pop_front()
            };

            match task {
                Some(task) => {
                    println!("Worker {} is executing a task.", self.id);
                    task();
                }
                None => {
                    println!("Worker {} found no tasks, trying to steal.", self.id);
                    // 尝试窃取其他工作者的任务
                    // ... 这里可以实现窃取逻辑 ...
                    break; // 这里为了示例，直接退出
                }
            }
        }
    }
}

struct ThreadPool {
    workers: Arc<Vec<Arc<Worker>>>,
    task_queue: Arc<Mutex<VecDeque<Box<dyn FnOnce() + Send + 'static>>>>,
}

impl ThreadPool {
    fn new(size: usize) -> Self {
        let task_queue = Arc::new(Mutex::new(VecDeque::new()));
        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            let worker = Arc::new(Worker::new(id, Arc::clone(&task_queue)));
            workers.push(worker);
        }

        ThreadPool {
            workers: Arc::new(workers),
            task_queue,
        }
    }

    fn execute<F>(&self, task: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let mut queue = self.task_queue.lock().unwrap();
        queue.push_back(Box::new(task));
    }

    fn run(&self) {
        let mut handles = vec![];

        for worker in self.workers.iter() {
            let worker = Arc::clone(worker);
            let handle = thread::spawn(move || {
                worker.work();
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }
    }
}

#[allow(unused)]
pub fn work_stealing_test() {
    let pool = ThreadPool::new(4);

    for i in 0..10 {
        pool.execute(move || {
            println!("Task {} is running.", i);
        });
    }

    pool.run();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_work_stealing01() {
        work_stealing_test();
    }
}
