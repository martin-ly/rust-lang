use std::collections::VecDeque;

#[allow(unused)]
// 定义一个对象池结构体
struct ObjectPool<T> {
    pool: VecDeque<T>,
}


impl<T> ObjectPool<T> {
    // 创建一个新的对象池
    fn new() -> Self {
        ObjectPool {
            pool: VecDeque::new(),
        }
    }

    // 从池中获取一个对象
    fn get(&mut self) -> Option<T> {
        self.pool.pop_front()
    }

    // 将对象返回到池中
    fn put(&mut self, item: T) {
        self.pool.push_back(item);
    }

    // 添加对象到池中
    fn add(&mut self, item: T) {
        self.pool.push_back(item);
    }
}

#[allow(unused)]
// 示例对象
#[derive(Debug)]
struct MyObject {
    id: u32,
}

#[allow(unused)]
pub fn test_object_pool() {
    let mut pool = ObjectPool::new();

    // 向池中添加对象
    pool.add(MyObject { id: 1 });
    pool.add(MyObject { id: 2 });

    // 从池中获取对象
    if let Some(obj) = pool.get() {
        println!("获取到对象: {:?}", obj);
    }

    // 将对象返回到池中
    pool.put(MyObject { id: 3 });

    // 再次获取对象
    if let Some(obj) = pool.get() {
        println!("获取到对象: {:?}", obj);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_object_pool01() {
        test_object_pool();
    }
}

