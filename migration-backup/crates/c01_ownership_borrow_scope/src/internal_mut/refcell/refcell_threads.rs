use std::cell::RefCell;
use std::sync::{Arc, Mutex};
use std::thread;

/*
结合使用的场景
    Arc：
        用于在多个线程之间安全地共享数据。
        它是一个原子引用计数的智能指针，允许多个所有者共享同一数据。
    Mutex：
        用于在多线程环境中保护数据，确保同一时间只有一个线程可以访问数据。
    RwLock：
        允许多个读者或一个写者访问数据，适用于读多写少的场景。
    RefCell：
        允许在单线程环境中进行内部可变性，适用于需要在不可变上下文中修改数据的情况。

实现更复杂的内部可变性和线程安全的共享数据结构.
*/

#[allow(unused)]
struct Data {
    value: RefCell<i32>,
}

#[allow(unused)]
impl Data {
    fn new(value: i32) -> Self {
        Data {
            value: RefCell::new(value),
        }
    }

    fn increment(&self) {
        *self.value.borrow_mut() += 1;
    }
}

/*
解释
    Data结构体：
        使用RefCell<i32>来存储一个可变的整数值。
    Arc和Mutex：
        将Data包装在Arc<Mutex<Data>>中，以便在多个线程之间共享和保护数据。
    increment方法：
        通过borrow_mut()获取可变引用并增加值。
    多线程：
        在多个线程中克隆Arc，并通过Mutex锁定数据以安全地调用increment方法。
    最终值：
        在所有线程完成后，读取并打印最终值。
*/

#[allow(unused)]
fn refcell_threads() {
    let data = Arc::new(Mutex::new(Data::new(0)));
    let mut handles = vec![];

    for _ in 0..10 {
        let data_clone = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let data = data_clone.lock().unwrap();
            data.increment();
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 读取最终值
    let data01 = data.lock().unwrap();
    let final_value = data01.value.borrow();
    // 输出: Final Value: 10
    println!("Final Value: {}", final_value);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_refcell_threads01() {
        refcell_threads();
    }
}
