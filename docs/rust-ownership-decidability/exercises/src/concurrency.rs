//! Concurrency Examples
//!
//! Demonstrates Send, Sync, Arc, Mutex, and thread safety.

use std::sync::{Arc, Mutex};
use std::thread;

/// Example 1: Thread Spawning
/// 
/// Creating a new thread with spawn.
/// ```
/// use rust_ownership_decidability::concurrency::spawn_demo;
/// spawn_demo();
/// ```
pub fn spawn_demo() {
    let handle = thread::spawn(|| {
        println!("Hello from spawned thread!");
    });
    
    println!("Hello from main thread!");
    handle.join().unwrap();
}

/// Example 2: Move Closure
/// 
/// Transferring ownership to a thread.
pub fn move_closure_demo() {
    let data = String::from("hello");
    
    let handle = thread::spawn(move || {
        println!("Data in thread: {}", data);
    });
    
    // data is no longer accessible here
    handle.join().unwrap();
}

/// Example 3: Shared State with Arc
/// 
/// Atomic Reference Counting for thread-safe sharing.
/// ```
/// use rust_ownership_decidability::concurrency::arc_demo;
/// arc_demo();
/// ```
pub fn arc_demo() {
    let data = Arc::new(vec![1, 2, 3]);
    let mut handles = vec![];
    
    for i in 0..3 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            println!("Thread {}: {:?}", i, data);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}

/// Example 4: Mutex for Mutable Shared State
/// 
/// Mutual exclusion for safe mutation across threads.
/// ```
/// use rust_ownership_decidability::concurrency::mutex_demo;
/// mutex_demo();
/// ```
pub fn mutex_demo() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Result: {}", *counter.lock().unwrap());
}

/// Example 5: Send and Sync Traits
/// 
/// Understanding auto-trait bounds.
/// 
/// - Send: Safe to transfer ownership between threads
/// - Sync: Safe to share references between threads
/// 
/// Most types are Send + Sync. Exceptions include Rc and raw pointers.

/// Example 6: Scoped Threads
/// 
/// Threads that can borrow local data.
/// ```
/// use rust_ownership_decidability::concurrency::scoped_threads_demo;
/// scoped_threads_demo();
/// ```
pub fn scoped_threads_demo() {
    let data = vec![1, 2, 3, 4, 5];
    
    thread::scope(|s| {
        s.spawn(|| {
            println!("Sum: {}", data.iter().sum::<i32>());
        });
        
        s.spawn(|| {
            println!("First: {}", data[0]);
        });
    });
    
    // data is still valid here
    println!("Data: {:?}", data);
}

/// Example 7: Deadlock Prevention
/// 
/// Strategies to avoid deadlocks.
pub fn deadlock_prevention() {
    let lock1 = Arc::new(Mutex::new(1));
    let lock2 = Arc::new(Mutex::new(2));
    
    // Consistent ordering prevents deadlock
    let t1 = {
        let (l1, l2) = (Arc::clone(&lock1), Arc::clone(&lock2));
        thread::spawn(move || {
            let _a = l1.lock().unwrap();
            let _b = l2.lock().unwrap();
            println!("Thread 1 acquired both locks");
        })
    };
    
    let t2 = {
        let (l1, l2) = (Arc::clone(&lock1), Arc::clone(&lock2));
        // Same order as t1!
        thread::spawn(move || {
            let _a = l1.lock().unwrap();
            let _b = l2.lock().unwrap();
            println!("Thread 2 acquired both locks");
        })
    };
    
    t1.join().unwrap();
    t2.join().unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_arc_sharing() {
        let data = Arc::new(5);
        let mut handles = vec![];
        
        for _ in 0..5 {
            let data = Arc::clone(&data);
            handles.push(thread::spawn(move || {
                assert_eq!(*data, 5);
            }));
        }
        
        for handle in handles {
            handle.join().unwrap();
        }
    }

    #[test]
    fn test_mutex_counter() {
        let counter = Arc::new(Mutex::new(0));
        let mut handles = vec![];
        
        for _ in 0..10 {
            let counter = Arc::clone(&counter);
            handles.push(thread::spawn(move || {
                let mut num = counter.lock().unwrap();
                *num += 1;
            }));
        }
        
        for handle in handles {
            handle.join().unwrap();
        }
        
        assert_eq!(*counter.lock().unwrap(), 10);
    }

    #[test]
    fn test_scoped_threads() {
        let data = vec![1, 2, 3];
        
        thread::scope(|s| {
            s.spawn(|| {
                assert_eq!(data.len(), 3);
            });
        });
        
        // data still valid
        assert_eq!(data, vec![1, 2, 3]);
    }
}
