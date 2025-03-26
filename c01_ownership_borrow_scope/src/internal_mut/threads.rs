use std::sync::{Arc, Mutex};
use std::thread;

/*
使用 Arc<Mutex<T>>
    Arc 是一个原子引用计数的智能指针，允许多个所有者共享同一个值，而 Mutex 提供线程安全的互斥访问。
    可以在多个线程中共享同一个值，并在需要时对其进行修改。
*/

#[allow(unused)]
struct MyStruct {
    value: i32,
}

impl MyStruct {
    fn update(&mut self, new_value: i32) {
        self.value = new_value;
    }
}

#[allow(unused)]
pub fn threads_test() {
    let my_struct = Arc::new(Mutex::new(MyStruct { value: 0 }));

    let my_struct_clone01 = Arc::clone(&my_struct);
    let handle01 = thread::spawn(move || {
        let mut borrowed = my_struct_clone01.lock().unwrap();
        borrowed.update(10);
    });

    let my_struct_clone02 = Arc::clone(&my_struct);
    let handle02 = thread::spawn(move || {
        let mut borrowed = my_struct_clone02.lock().unwrap();
        borrowed.update(20);
    });

    // 读取值
    println!("Value: {}", my_struct.lock().unwrap().value);
    handle01.join().unwrap();

    // 读取值
    handle02.join().unwrap();
    // 读取值
    println!("Value: {}", my_struct.lock().unwrap().value);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_threads01() {
        threads_test();
    }
}
