use std::sync::OnceLock;

pub struct Singleton<T> {
    instance: OnceLock<T>,
}

impl<T> Singleton<T> {
    pub fn new() -> Self {
        Singleton {
            instance: OnceLock::new(),
        }
    }

    pub fn get_instance<F>(&self, initializer: F) -> &T
    where
        F: FnOnce() -> T,
    {
        self.instance.get_or_init(initializer)
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_singleton01() {
        test_singleton();
    }
}
