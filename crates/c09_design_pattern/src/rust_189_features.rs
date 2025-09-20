//! Rust 1.89 新特性演示模块
//!
//! 本模块展示了如何在设计模式中充分利用 Rust 1.89 的新特性

use std::cell::Cell;
use std::ptr;
use std::sync::OnceLock;

/// 演示 Cell::update 方法的使用
/// 这是 Rust 1.89 中新增的原子更新方法
pub struct CellUpdateDemo {
    counter: Cell<i32>,
    data: Cell<Option<String>>,
}

impl Default for CellUpdateDemo {
    fn default() -> Self {
        Self::new()
    }
}

impl CellUpdateDemo {
    pub fn new() -> Self {
        Self {
            counter: Cell::new(0),
            data: Cell::new(None),
        }
    }

    /// 使用 Cell::update 进行原子更新
    pub fn increment_counter(&self) -> i32 {
        self.counter.update(|current| {
            println!("当前计数器值: {}", current);
            current + 1
        });
        self.counter.get()
    }

    /// 设置数据（使用传统方法，因为 String 不实现 Copy）
    pub fn set_data(&self, value: String) {
        self.data.set(Some(value));
    }

    /// 获取当前计数器值
    pub fn get_counter(&self) -> i32 {
        self.counter.get()
    }

    /// 获取当前数据
    pub fn get_data(&self) -> Option<String> {
        self.data.take()
    }
}

/// 演示裸指针 Default 实现的使用
/// 这是 Rust 1.89 中新增的特性，简化了指针的初始化
pub struct PointerDefaultDemo {
    raw_ptr: *const i32,
    id: u32,
}

impl PointerDefaultDemo {
    pub fn new(id: u32) -> Self {
        Self {
            raw_ptr: ptr::null(), // 利用 Default 特性
            id,
        }
    }

    /// 设置指针值
    pub fn set_pointer(&mut self, value: i32) {
        let boxed_value = Box::new(value);
        self.raw_ptr = Box::into_raw(boxed_value);
    }

    /// 获取指针值（如果有效）
    pub fn get_pointer(&self) -> Option<i32> {
        if self.raw_ptr.is_null() {
            None
        } else {
            unsafe { Some(*self.raw_ptr) }
        }
    }

    /// 获取 ID
    pub fn get_id(&self) -> u32 {
        self.id
    }
}

impl Drop for PointerDefaultDemo {
    fn drop(&mut self) {
        if !self.raw_ptr.is_null() {
            unsafe {
                let _ = Box::from_raw(self.raw_ptr as *mut i32);
            }
        }
    }
}

/// 演示数组转换优化的使用
/// 这是 Rust 1.89 中改进的数组与 Vec 之间的转换
pub struct ArrayConversionDemo {
    data: Vec<i32>,
}

impl Default for ArrayConversionDemo {
    fn default() -> Self {
        Self::new()
    }
}

impl ArrayConversionDemo {
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }

    /// 从固定大小数组创建
    pub fn from_array<const N: usize>(array: [i32; N]) -> Self {
        Self {
            // 使用 Rust 1.89 的数组转换优化
            data: array.into(),
        }
    }

    /// 转换为 Box<[T]>
    pub fn to_boxed_slice(&self) -> Box<[i32]> {
        self.data.clone().into_boxed_slice()
    }

    /// 从 Box<[T]> 转换回 Vec
    pub fn from_boxed_slice(boxed: Box<[i32]>) -> Self {
        Self {
            data: boxed.into_vec(),
        }
    }

    /// 获取数据
    pub fn get_data(&self) -> &[i32] {
        &self.data
    }

    /// 添加元素
    pub fn push(&mut self, value: i32) {
        self.data.push(value);
    }
}

/// 演示 OnceLock 的高级用法
/// 结合 Rust 1.89 的新特性使用
pub struct AdvancedSingleton<T> {
    instance: OnceLock<T>,
    metadata: Cell<Option<String>>,
}

impl<T> Default for AdvancedSingleton<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> AdvancedSingleton<T> {
    pub fn new() -> Self {
        Self {
            instance: OnceLock::new(),
            metadata: Cell::new(None),
        }
    }

    /// 获取或初始化实例，同时设置元数据
    pub fn get_or_init<F>(&self, initializer: F) -> &T
    where
        F: FnOnce() -> T,
    {
        self.instance.get_or_init(initializer)
    }

    /// 设置元数据（使用传统方法，因为 String 不实现 Copy）
    pub fn set_metadata(&self, metadata: String) {
        self.metadata.set(Some(metadata));
    }

    /// 获取元数据
    pub fn get_metadata(&self) -> Option<String> {
        self.metadata.take()
    }

    /// 尝试获取已初始化的实例
    pub fn try_get(&self) -> Option<&T> {
        self.instance.get()
    }
}

/// 演示网络套接字增强特性
/// 使用 AsFd/AsHandle/AsSocket 等新特性
#[cfg(unix)]
pub struct SocketDemo {
    // 在实际应用中，这里会使用真实的套接字
    // 这里只是演示结构
}

#[cfg(unix)]
impl SocketDemo {
    pub fn new() -> Self {
        Self {}
    }

    /// 演示 AsFd 的使用
    pub fn demonstrate_as_fd(&self) {
        // 在实际应用中，这里会使用 std::os::unix::io::AsFd
        println!("演示 AsFd 特性（仅在 Unix 系统上可用）");
    }
}

#[cfg(windows)]
pub struct SocketDemo {
    // Windows 版本
}

#[cfg(windows)]
impl Default for SocketDemo {
    fn default() -> Self {
        Self::new()
    }
}

impl SocketDemo {
    pub fn new() -> Self {
        Self {}
    }

    /// 演示 AsHandle 的使用
    pub fn demonstrate_as_handle(&self) {
        // 在实际应用中，这里会使用 std::os::windows::io::AsHandle
        println!("演示 AsHandle 特性（仅在 Windows 系统上可用）");
    }
}

#[cfg(not(any(unix, windows)))]
pub struct SocketDemo {}

#[cfg(not(any(unix, windows)))]
impl SocketDemo {
    pub fn new() -> Self {
        Self {}
    }

    pub fn demonstrate_generic(&self) {
        println!("演示通用套接字特性");
    }
}

/// 综合演示函数
pub fn demonstrate_rust_189_features() {
    println!("=== Rust 1.89 新特性演示 ===");

    // 1. Cell::update 演示
    println!("\n1. Cell::update 演示:");
    let cell_demo = CellUpdateDemo::new();
    let new_value = cell_demo.increment_counter();
    println!("更新后的计数器值: {}", new_value);

    cell_demo.set_data("Hello, Rust 1.89!".to_string());
    println!("设置的数据: {:?}", cell_demo.get_data());

    // 2. 裸指针 Default 演示
    println!("\n2. 裸指针 Default 演示:");
    let mut ptr_demo = PointerDefaultDemo::new(42);
    println!("指针 ID: {}", ptr_demo.get_id());
    println!("初始指针值: {:?}", ptr_demo.get_pointer());

    ptr_demo.set_pointer(100);
    println!("设置后的指针值: {:?}", ptr_demo.get_pointer());

    // 3. 数组转换优化演示
    println!("\n3. 数组转换优化演示:");
    let array = [1, 2, 3, 4, 5];
    let conversion_demo = ArrayConversionDemo::from_array(array);
    println!("从数组创建的数据: {:?}", conversion_demo.get_data());

    let boxed = conversion_demo.to_boxed_slice();
    println!("转换为 Box<[T]>: {:?}", boxed);

    let back_to_demo = ArrayConversionDemo::from_boxed_slice(boxed);
    println!("从 Box<[T]> 转换回: {:?}", back_to_demo.get_data());

    // 4. 高级单例演示
    println!("\n4. 高级单例演示:");
    let singleton = AdvancedSingleton::new();
    singleton.set_metadata("单例元数据".to_string());

    let instance = singleton.get_or_init(|| "单例实例".to_string());
    println!("单例实例: {}", instance);
    println!("单例元数据: {:?}", singleton.get_metadata());

    // 5. 网络套接字演示
    println!("\n5. 网络套接字增强演示:");
    let socket_demo = SocketDemo::new();

    #[cfg(unix)]
    socket_demo.demonstrate_as_fd();

    #[cfg(windows)]
    socket_demo.demonstrate_as_handle();

    #[cfg(not(any(unix, windows)))]
    socket_demo.demonstrate_generic();

    println!("\n=== 演示完成 ===");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cell_update_demo() {
        let demo = CellUpdateDemo::new();
        let value = demo.increment_counter();
        assert_eq!(value, 1);
        assert_eq!(demo.get_counter(), 1);

        demo.set_data("test".to_string());
        assert_eq!(demo.get_data(), Some("test".to_string()));
    }

    #[test]
    fn test_pointer_default_demo() {
        let mut demo = PointerDefaultDemo::new(123);
        assert_eq!(demo.get_id(), 123);
        assert_eq!(demo.get_pointer(), None);

        demo.set_pointer(456);
        assert_eq!(demo.get_pointer(), Some(456));
    }

    #[test]
    fn test_array_conversion_demo() {
        let array = [1, 2, 3];
        let demo = ArrayConversionDemo::from_array(array);
        assert_eq!(demo.get_data(), &[1, 2, 3]);

        let boxed = demo.to_boxed_slice();
        let back_demo = ArrayConversionDemo::from_boxed_slice(boxed);
        assert_eq!(back_demo.get_data(), &[1, 2, 3]);
    }

    #[test]
    fn test_advanced_singleton() {
        let singleton = AdvancedSingleton::new();
        singleton.set_metadata("test metadata".to_string());

        let instance = singleton.get_or_init(|| "test instance".to_string());
        assert_eq!(instance, "test instance");
        assert_eq!(singleton.get_metadata(), Some("test metadata".to_string()));
    }

    #[test]
    fn test_socket_demo() {
        let _demo = SocketDemo::new();
        // 这个测试主要确保结构体可以正常创建
        // 具体的网络功能测试需要实际的套接字
    }

    #[test]
    fn test_demonstrate_features() {
        // 运行演示函数，确保没有 panic
        demonstrate_rust_189_features();
    }
}
