//! GAT（泛型关联类型）示例
//!
//! 本示例展示GAT（Generic Associated Types）的使用：
//! - GAT的基本语法
//! - 借用迭代器（Lending Iterator）
//! - 实际应用场景
//!
//! 运行方式:
//! ```bash
//! cargo run --example generic_gat_demo
//! ```

/// 使用GAT的迭代器trait
trait LendingIterator {
    type Item<'a>
    where
        Self: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

/// 窗口迭代器
struct WindowsIterator<T> {
    data: Vec<T>,
    window_size: usize,
    position: usize,
}

impl<T> WindowsIterator<T> {
    fn new(data: Vec<T>, window_size: usize) -> Self {
        Self {
            data,
            window_size,
            position: 0,
        }
    }
}

impl<T> LendingIterator for WindowsIterator<T> {
    type Item<'a> = &'a [T]
    where
        T: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>> {
        if self.position + self.window_size <= self.data.len() {
            let start = self.position;
            let end = start + self.window_size;
            self.position += 1;
            Some(&self.data[start..end])
        } else {
            None
        }
    }
}

/// 使用GAT的容器trait
trait Container {
    type Item<'a>
    where
        Self: 'a;

    fn get<'a>(&'a self, index: usize) -> Option<Self::Item<'a>>;
}

/// 向量容器
struct VecContainer<T> {
    items: Vec<T>,
}

impl<T> VecContainer<T> {
    fn new(items: Vec<T>) -> Self {
        Self { items }
    }
}

impl<T> Container for VecContainer<T> {
    type Item<'a> = &'a T
    where
        T: 'a;

    fn get<'a>(&'a self, index: usize) -> Option<Self::Item<'a>> {
        self.items.get(index)
    }
}

fn main() {
    println!("🚀 GAT（泛型关联类型）示例\n");
    println!("{}", "=".repeat(60));

    // 1. 使用LendingIterator
    println!("\n📊 LendingIterator 示例:");
    println!("{}", "-".repeat(60));
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let mut windows = WindowsIterator::new(data, 3);

    println!("窗口大小: 3");
    let mut count = 0;
    while let Some(window) = windows.next() {
        count += 1;
        println!("窗口 {}: {:?}", count, window);
        if count >= 5 {
            break;
        }
    }

    // 2. 使用Container
    println!("\n📊 Container 示例:");
    println!("{}", "-".repeat(60));
    let container = VecContainer::new(vec![10, 20, 30, 40, 50]);

    for i in 0..5 {
        if let Some(item) = container.get(i) {
            println!("索引 {}: {}", i, item);
        }
    }

    // 3. 字符串容器示例
    println!("\n📊 字符串容器示例:");
    println!("{}", "-".repeat(60));
    let str_container = VecContainer::new(vec!["Hello", "World", "Rust", "GAT"]);

    for i in 0..str_container.items.len() {
        if let Some(item) = str_container.get(i) {
            println!("索引 {}: {}", i, item);
        }
    }

    println!("\n✅ 演示完成！");
}
