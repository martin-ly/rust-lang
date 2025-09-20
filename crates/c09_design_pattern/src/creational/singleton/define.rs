use std::cell::Cell;
use std::sync::OnceLock;

/// 使用Rust 1.89新特性优化的单例模式实现
///
/// 特性：
/// - 使用OnceLock确保线程安全的单例初始化
/// - 支持Cell::update进行原子更新操作
/// - 提供多种初始化方式
pub struct Singleton<T> {
    instance: OnceLock<T>,
}

/// 支持Cell更新的单例变体
pub struct CellSingleton<T> {
    instance: Cell<Option<T>>,
}

impl<T> Singleton<T> {
    pub fn new() -> Self {
        Singleton {
            instance: OnceLock::new(),
        }
    }

    /// 获取单例实例，使用闭包进行延迟初始化
    pub fn get_instance<F>(&self, initializer: F) -> &T
    where
        F: FnOnce() -> T,
    {
        self.instance.get_or_init(initializer)
    }

    /// 尝试获取已初始化的实例
    pub fn try_get_instance(&self) -> Option<&T> {
        self.instance.get()
    }
}

impl<T> CellSingleton<T> {
    pub fn new() -> Self {
        CellSingleton {
            instance: Cell::new(None),
        }
    }

    /// 使用Cell::update进行原子更新
    pub fn get_or_init<F>(&self, initializer: F) -> T
    where
        F: FnOnce() -> T,
        T: Clone + Copy,
    {
        self.instance
            .update(|current| Some(current.unwrap_or_else(initializer)));
        self.instance.get().unwrap()
    }
}

impl<T> Default for Singleton<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Default for CellSingleton<T> {
    fn default() -> Self {
        Self::new()
    }
}

// 示例使用
#[allow(unused)]
pub fn test_singleton() {
    let singleton = Singleton::new();

    let instance = singleton.get_instance(|| {
        // 这里可以初始化您的实例
        String::from("这是单例实例")
    });

    println!("{}", instance);

    // 测试多次获取同一实例
    let instance2 = singleton.get_instance(|| String::from("这不应该被调用"));

    assert_eq!(instance, instance2);
    println!("单例模式验证成功：两次获取的是同一个实例");
}

/// 演示Cell::update的使用
#[allow(unused)]
pub fn test_cell_update() {
    use std::cell::Cell;

    let cell = Cell::new(0);

    // 使用Cell::update进行原子更新
    cell.update(|current| {
        println!("当前值: {}", current);
        current + 1
    });

    println!("更新后的值: {:?}", ());
    println!("Cell中的值: {}", cell.get());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_singleton01() {
        test_singleton();
    }

    #[test]
    fn test_cell_update_demo() {
        test_cell_update();
    }

    #[test]
    fn test_singleton_thread_safety() {
        use std::sync::Arc;
        use std::thread;

        let singleton = Arc::new(Singleton::new());
        let mut handles = vec![];

        for i in 0..10 {
            let singleton_clone = Arc::clone(&singleton);
            let handle = thread::spawn(move || {
                let instance = singleton_clone.get_instance(|| format!("线程 {} 初始化", i));
                instance.clone()
            });
            handles.push(handle);
        }

        let results: Vec<String> = handles.into_iter().map(|h| h.join().unwrap()).collect();

        // 所有线程应该得到相同的实例
        let first_result = &results[0];
        for result in &results {
            assert_eq!(first_result, result);
        }
    }
}
