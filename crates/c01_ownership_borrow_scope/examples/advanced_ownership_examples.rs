//! # 高级所有权和借用示例 / Advanced Ownership and Borrowing Examples
//!
//! 本示例展示了 Rust 1.90 版本中所有权和借用系统的高级用法，
//! 包括复杂的所有权模式、高级借用技巧和最佳实践。
//! This example demonstrates advanced usage of Rust 1.90's ownership and borrowing system,
//! including complex ownership patterns, advanced borrowing techniques, and best practices.

use std::collections::HashMap;
use std::rc::{Rc, Weak};
use std::sync::{Arc, Mutex, RwLock};
use std::cell::RefCell;
use std::thread;
use std::time::Duration;

/// # 1. 复杂所有权模式 / Complex Ownership Patterns

/// ## 1.1 所有权转移链 / Ownership Transfer Chain
/// 
/// 演示所有权如何在多个函数和结构体之间转移
/// Demonstrates how ownership transfers between multiple functions and structs

pub mod ownership_transfer_chain {
    use super::*;

    /// 数据容器 / Data Container
    #[derive(Debug, Clone)]
    pub struct DataContainer {
        pub id: u32,
        pub data: String,
        pub metadata: HashMap<String, String>,
    }

    impl DataContainer {
        /// 创建新的数据容器 / Create new data container
        pub fn new(id: u32, data: String) -> Self {
            let mut metadata = HashMap::new();
            metadata.insert("created_at".to_string(), "2025-01-01".to_string());
            metadata.insert("version".to_string(), "1.0".to_string());
            
            Self {
                id,
                data,
                metadata,
            }
        }
        
        /// 添加元数据 / Add metadata
        pub fn add_metadata(&mut self, key: String, value: String) {
            self.metadata.insert(key, value);
        }
        
        /// 获取数据长度 / Get data length
        pub fn get_data_length(&self) -> usize {
            self.data.len()
        }
    }

    /// 所有权转移链示例 / Ownership Transfer Chain Example
    pub fn ownership_transfer_chain_example() {
        println!("=== 所有权转移链示例 / Ownership Transfer Chain Example ===");
        
        // 创建数据容器 / Create data container
        let container = DataContainer::new(1, "Hello, World!".to_string());
        println!("Created container: {:?}", container);
        
        // 第一次转移 / First transfer
        let container = process_container(container);
        println!("After first processing: {:?}", container);
        
        // 第二次转移 / Second transfer
        let container = enhance_container(container);
        println!("After enhancement: {:?}", container);
        
        // 第三次转移 / Third transfer
        let final_result = finalize_container(container);
        println!("Final result: {:?}", final_result);
    }

    /// 处理容器 / Process container
    fn process_container(mut container: DataContainer) -> DataContainer {
        container.add_metadata("processed".to_string(), "true".to_string());
        container.add_metadata("process_time".to_string(), "2025-01-01T10:00:00Z".to_string());
        container
    }

    /// 增强容器 / Enhance container
    fn enhance_container(mut container: DataContainer) -> DataContainer {
        container.add_metadata("enhanced".to_string(), "true".to_string());
        container.add_metadata("enhancement_level".to_string(), "high".to_string());
        container
    }

    /// 完成容器 / Finalize container
    fn finalize_container(mut container: DataContainer) -> DataContainer {
        container.add_metadata("finalized".to_string(), "true".to_string());
        container.add_metadata("finalization_time".to_string(), "2025-01-01T11:00:00Z".to_string());
        container
    }
}

/// ## 1.2 所有权共享模式 / Ownership Sharing Patterns
/// 
/// 演示如何使用智能指针实现所有权共享
/// Demonstrates how to use smart pointers for ownership sharing

pub mod ownership_sharing_patterns {
    use super::*;

    /// 共享数据节点 / Shared Data Node
    #[derive(Debug)]
    pub struct SharedNode {
        pub id: u32,
        pub data: String,
        pub children: Vec<Rc<RefCell<SharedNode>>>,
        pub parent: Option<Weak<RefCell<SharedNode>>>,
    }

    impl SharedNode {
        /// 创建新节点 / Create new node
        pub fn new(id: u32, data: String) -> Rc<RefCell<Self>> {
            Rc::new(RefCell::new(Self {
                id,
                data,
                children: Vec::new(),
                parent: None,
            }))
        }
        
        /// 添加子节点 / Add child node
        pub fn add_child(parent: &Rc<RefCell<Self>>, child: Rc<RefCell<Self>>) {
            // 设置子节点的父引用 / Set child's parent reference
            child.borrow_mut().parent = Some(Rc::downgrade(parent));
            
            // 添加子节点到父节点 / Add child to parent
            parent.borrow_mut().children.push(child);
        }
        
        /// 获取所有后代节点 / Get all descendant nodes
        pub fn get_descendants(&self) -> Vec<u32> {
            let mut descendants = Vec::new();
            
            for child in &self.children {
                descendants.push(child.borrow().id);
                descendants.extend(child.borrow().get_descendants());
            }
            
            descendants
        }
        
        /// 获取根节点 / Get root node
        pub fn get_root(&self) -> Option<Rc<RefCell<Self>>> {
            if let Some(parent_weak) = &self.parent
                && let Some(parent_strong) = parent_weak.upgrade() {
                    return parent_strong.borrow().get_root();
                }
            None
        }
    }

    /// 所有权共享模式示例 / Ownership Sharing Patterns Example
    pub fn ownership_sharing_patterns_example() {
        println!("=== 所有权共享模式示例 / Ownership Sharing Patterns Example ===");
        
        // 创建根节点 / Create root node
        let root = SharedNode::new(1, "Root Node".to_string());
        println!("Created root node: {:?}", root.borrow());
        
        // 创建子节点 / Create child nodes
        let child1 = SharedNode::new(2, "Child 1".to_string());
        let child2 = SharedNode::new(3, "Child 2".to_string());
        
        // 添加子节点 / Add child nodes
        SharedNode::add_child(&root, child1);
        SharedNode::add_child(&root, child2);
        
        // 创建孙节点 / Create grandchild nodes
        let grandchild1 = SharedNode::new(4, "Grandchild 1".to_string());
        let grandchild2 = SharedNode::new(5, "Grandchild 2".to_string());
        
        // 添加孙节点到第一个子节点 / Add grandchildren to first child
        if let Some(first_child) = root.borrow().children.first() {
            SharedNode::add_child(first_child, grandchild1);
            SharedNode::add_child(first_child, grandchild2);
        }
        
        // 显示树结构 / Display tree structure
        println!("Tree structure:");
        print_tree(&root, 0);
        
        // 获取后代节点 / Get descendant nodes
        let descendants = root.borrow().get_descendants();
        println!("Descendants of root: {:?}", descendants);
        
        // 演示弱引用 / Demonstrate weak references
        if let Some(first_child) = root.borrow().children.first() {
            let weak_ref = Rc::downgrade(first_child);
            println!("Weak reference count: {}", Rc::weak_count(first_child));
            
            if let Some(strong_ref) = weak_ref.upgrade() {
                println!("Successfully upgraded weak reference: {:?}", strong_ref.borrow().id);
            }
        }
    }

    /// 打印树结构 / Print tree structure
    fn print_tree(node: &Rc<RefCell<SharedNode>>, depth: usize) {
        let indent = "  ".repeat(depth);
        let node_data = node.borrow();
        println!("{}{}: {}", indent, node_data.id, node_data.data);
        
        for child in &node_data.children {
            print_tree(child, depth + 1);
        }
    }
}

/// # 2. 高级借用技巧 / Advanced Borrowing Techniques

/// ## 2.1 复杂借用模式 / Complex Borrowing Patterns
/// 
/// 演示复杂的借用模式和多层借用
/// Demonstrates complex borrowing patterns and multi-level borrowing

pub mod complex_borrowing_patterns {
    use super::*;

    /// 复杂数据结构 / Complex Data Structure
    #[derive(Debug)]
    pub struct ComplexData {
        pub id: u32,
        pub data: Vec<String>,
        pub metadata: HashMap<String, String>,
        pub nested: Option<Box<ComplexData>>,
    }

    impl ComplexData {
        /// 创建新的复杂数据 / Create new complex data
        pub fn new(id: u32) -> Self {
            Self {
                id,
                data: Vec::new(),
                metadata: HashMap::new(),
                nested: None,
            }
        }
        
        /// 添加数据 / Add data
        pub fn add_data(&mut self, item: String) {
            self.data.push(item);
        }
        
        /// 添加元数据 / Add metadata
        pub fn add_metadata(&mut self, key: String, value: String) {
            self.metadata.insert(key, value);
        }
        
        /// 设置嵌套数据 / Set nested data
        pub fn set_nested(&mut self, nested: ComplexData) {
            self.nested = Some(Box::new(nested));
        }
    }

    /// 复杂借用模式示例 / Complex Borrowing Patterns Example
    pub fn complex_borrowing_patterns_example() {
        println!("=== 复杂借用模式示例 / Complex Borrowing Patterns Example ===");
        
        let mut complex_data = ComplexData::new(1);
        complex_data.add_data("Item 1".to_string());
        complex_data.add_data("Item 2".to_string());
        complex_data.add_metadata("type".to_string(), "complex".to_string());
        
        // 创建嵌套数据 / Create nested data
        let mut nested_data = ComplexData::new(2);
        nested_data.add_data("Nested Item 1".to_string());
        nested_data.add_metadata("type".to_string(), "nested".to_string());
        complex_data.set_nested(nested_data);
        
        // 演示复杂借用 / Demonstrate complex borrowing
        demonstrate_complex_borrowing(&mut complex_data);
        
        // 演示借用检查器的智能分析 / Demonstrate borrow checker's intelligent analysis
        demonstrate_smart_borrow_analysis(&mut complex_data);
    }

    /// 演示复杂借用 / Demonstrate complex borrowing
    fn demonstrate_complex_borrowing(data: &mut ComplexData) {
        // 同时借用不同的字段 / Borrow different fields simultaneously
        let data_ref = &data.data;
        let metadata_ref = &data.metadata;
        
        println!("Data length: {}", data_ref.len());
        println!("Metadata count: {}", metadata_ref.len());
        
        // 在借用结束后修改数据 / Modify data after borrows end
        data.add_data("New Item".to_string());
        data.add_metadata("new_key".to_string(), "new_value".to_string());
        
        println!("After modification - Data: {:?}", data.data);
        println!("After modification - Metadata: {:?}", data.metadata);
    }

    /// 演示智能借用分析 / Demonstrate smart borrow analysis
    fn demonstrate_smart_borrow_analysis(data: &mut ComplexData) {
        // Rust 1.90 的智能借用检查器可以分析更复杂的借用模式
        // Rust 1.90's smart borrow checker can analyze more complex borrowing patterns
        
        // 可以同时借用向量的不同部分 / Can borrow different parts of vector simultaneously
        if data.data.len() >= 2 {
            let data_len = data.data.len();
            let (first_half, second_half) = data.data.split_at_mut(data_len / 2);
            println!("First half: {:?}", first_half);
            println!("Second half: {:?}", second_half);
        }
        
        // 可以同时借用哈希映射的不同键 / Can borrow different keys of HashMap simultaneously
        if data.metadata.contains_key("type") && data.metadata.contains_key("new_key") {
            let type_value = data.metadata.get("type").unwrap();
            let new_key_value = data.metadata.get("new_key").unwrap();
            println!("Type: {}, New Key: {}", type_value, new_key_value);
        }
    }
}

/// ## 2.2 借用生命周期管理 / Borrow Lifetime Management
/// 
/// 演示如何管理复杂的借用生命周期
/// Demonstrates how to manage complex borrow lifetimes

pub mod borrow_lifetime_management {

    /// 生命周期管理器 / Lifetime Manager
    pub struct LifetimeManager<'a> {
        pub data: &'a mut Vec<String>,
        pub active_borrows: Vec<&'a str>,
    }

    impl<'a> LifetimeManager<'a> {
        /// 创建新的生命周期管理器 / Create new lifetime manager
        pub fn new(data: &'a mut Vec<String>) -> Self {
            Self {
                data,
                active_borrows: Vec::new(),
            }
        }
        
        /// 添加数据 / Add data
        pub fn add_data(&mut self, item: String) {
            self.data.push(item);
        }
        
        /// 获取数据引用 / Get data reference
        pub fn get_data_ref(&self) -> &Vec<String> {
            self.data
        }
        
        /// 获取可变数据引用 / Get mutable data reference
        pub fn get_data_mut(&mut self) -> &mut Vec<String> {
            self.data
        }
        
        /// 处理数据 / Process data
        pub fn process_data<F>(&mut self, processor: F) 
        where
            F: FnOnce(&mut Vec<String>),
        {
            processor(self.data);
        }
    }

    /// 借用生命周期管理示例 / Borrow Lifetime Management Example
    pub fn borrow_lifetime_management_example() {
        println!("=== 借用生命周期管理示例 / Borrow Lifetime Management Example ===");
        
        let mut data = vec![
            "Item 1".to_string(),
            "Item 2".to_string(),
            "Item 3".to_string(),
        ];
        
        // 创建生命周期管理器 / Create lifetime manager
        let mut manager = LifetimeManager::new(&mut data);
        
        // 添加数据 / Add data
        manager.add_data("Item 4".to_string());
        manager.add_data("Item 5".to_string());
        
        // 获取数据引用 / Get data reference
        let data_ref = manager.get_data_ref();
        println!("Data: {:?}", data_ref);
        
        // 处理数据 / Process data
        manager.process_data(|data| {
            data.push("Processed Item".to_string());
            data.sort();
        });
        
        // 获取最终数据 / Get final data
        let final_data = manager.get_data_ref();
        println!("Final data: {:?}", final_data);
        
        // 演示生命周期约束 / Demonstrate lifetime constraints
        demonstrate_lifetime_constraints();
    }

    /// 演示生命周期约束 / Demonstrate lifetime constraints
    fn demonstrate_lifetime_constraints() {
        let mut data1 = vec!["Data1".to_string()];
        let mut data2 = vec!["Data2".to_string()];
        
        // 函数可以接受不同生命周期的引用 / Function can accept references with different lifetimes
        let result = process_multiple_data(&mut data1, &mut data2);
        println!("Processed result: {:?}", result);
        
        // 演示生命周期推断 / Demonstrate lifetime inference
        let inferred_result = infer_lifetimes(&data1, &data2);
        println!("Inferred result: {:?}", inferred_result);
    }

    /// 处理多个数据 / Process multiple data
    fn process_multiple_data<'a, 'b>(
        data1: &'a mut Vec<String>,
        data2: &'b mut Vec<String>,
    ) -> (&'a Vec<String>, &'b Vec<String>) {
        data1.push("Processed1".to_string());
        data2.push("Processed2".to_string());
        (data1, data2)
    }

    /// 推断生命周期 / Infer lifetimes
    fn infer_lifetimes<'a>(data1: &'a Vec<String>, data2: &'a Vec<String>) -> &'a Vec<String> {
        if data1.len() > data2.len() {
            data1
        } else {
            data2
        }
    }
}

/// # 3. 并发所有权模式 / Concurrent Ownership Patterns

/// ## 3.1 线程间所有权共享 / Inter-thread Ownership Sharing
/// 
/// 演示如何在多个线程之间安全地共享所有权
/// Demonstrates how to safely share ownership between multiple threads

pub mod inter_thread_ownership_sharing {
    use super::*;

    /// 线程安全数据容器 / Thread-safe Data Container
    pub struct ThreadSafeContainer {
        pub data: Arc<Mutex<Vec<String>>>,
        pub counter: Arc<Mutex<u32>>,
        pub metadata: Arc<RwLock<HashMap<String, String>>>,
    }

    impl ThreadSafeContainer {
        /// 创建新的线程安全容器 / Create new thread-safe container
        pub fn new() -> Self {
            Self {
                data: Arc::new(Mutex::new(Vec::new())),
                counter: Arc::new(Mutex::new(0)),
                metadata: Arc::new(RwLock::new(HashMap::new())),
            }
        }
        
        /// 添加数据 / Add data
        pub fn add_data(&self, item: String) {
            let mut data = self.data.lock().unwrap();
            data.push(item);
            
            let mut counter = self.counter.lock().unwrap();
            *counter += 1;
        }
        
        /// 获取数据 / Get data
        pub fn get_data(&self) -> Vec<String> {
            let data = self.data.lock().unwrap();
            data.clone()
        }
        
        /// 获取计数器值 / Get counter value
        pub fn get_counter(&self) -> u32 {
            let counter = self.counter.lock().unwrap();
            *counter
        }
        
        /// 添加元数据 / Add metadata
        pub fn add_metadata(&self, key: String, value: String) {
            let mut metadata = self.metadata.write().unwrap();
            metadata.insert(key, value);
        }
        
        /// 获取元数据 / Get metadata
        pub fn get_metadata(&self, key: &str) -> Option<String> {
            let metadata = self.metadata.read().unwrap();
            metadata.get(key).cloned()
        }
    }

    /// 线程间所有权共享示例 / Inter-thread Ownership Sharing Example
    pub fn inter_thread_ownership_sharing_example() {
        println!("=== 线程间所有权共享示例 / Inter-thread Ownership Sharing Example ===");
        
        let container = Arc::new(ThreadSafeContainer::new());
        let mut handles = vec![];
        
        // 创建多个生产者线程 / Create multiple producer threads
        for i in 0..3 {
            let container_clone = Arc::clone(&container);
            let handle = thread::spawn(move || {
                for j in 0..5 {
                    let item = format!("Thread-{}-Item-{}", i, j);
                    container_clone.add_data(item);
                    container_clone.add_metadata(
                        format!("thread_{}_item_{}", i, j),
                        format!("Produced by thread {}", i)
                    );
                    thread::sleep(Duration::from_millis(10));
                }
            });
            handles.push(handle);
        }
        
        // 创建消费者线程 / Create consumer thread
        let container_clone = Arc::clone(&container);
        let consumer_handle = thread::spawn(move || {
            for _ in 0..10 {
                let data = container_clone.get_data();
                let counter = container_clone.get_counter();
                println!("Consumer sees {} items, counter: {}", data.len(), counter);
                thread::sleep(Duration::from_millis(50));
            }
        });
        
        // 等待所有线程完成 / Wait for all threads to complete
        for handle in handles {
            handle.join().unwrap();
        }
        consumer_handle.join().unwrap();
        
        // 显示最终结果 / Show final results
        let final_data = container.get_data();
        let final_counter = container.get_counter();
        println!("Final data count: {}", final_data.len());
        println!("Final counter: {}", final_counter);
        println!("Final data: {:?}", final_data);
    }
}

/// ## 3.2 原子所有权操作 / Atomic Ownership Operations
/// 
/// 演示如何使用原子操作进行所有权管理
/// Demonstrates how to use atomic operations for ownership management

pub mod atomic_ownership_operations {
    use super::*;
    use std::sync::atomic::{AtomicUsize, AtomicBool, Ordering};

    /// 原子所有权管理器 / Atomic Ownership Manager
    pub struct AtomicOwnershipManager {
        pub data: Arc<Mutex<Vec<String>>>,
        pub active_count: AtomicUsize,
        pub is_processing: AtomicBool,
        pub total_processed: AtomicUsize,
    }

    impl AtomicOwnershipManager {
        /// 创建新的原子所有权管理器 / Create new atomic ownership manager
        pub fn new() -> Self {
            Self {
                data: Arc::new(Mutex::new(Vec::new())),
                active_count: AtomicUsize::new(0),
                is_processing: AtomicBool::new(false),
                total_processed: AtomicUsize::new(0),
            }
        }
        
        /// 开始处理 / Start processing
        pub fn start_processing(&self) -> bool {
            // 使用原子操作检查是否可以开始处理 / Use atomic operation to check if processing can start
            if self.is_processing.compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst).is_ok() {
                self.active_count.fetch_add(1, Ordering::SeqCst);
                true
            } else {
                false
            }
        }
        
        /// 结束处理 / End processing
        pub fn end_processing(&self) {
            self.active_count.fetch_sub(1, Ordering::SeqCst);
            self.total_processed.fetch_add(1, Ordering::SeqCst);
            
            // 如果没有活跃的处理，重置处理标志 / If no active processing, reset processing flag
            if self.active_count.load(Ordering::SeqCst) == 0 {
                self.is_processing.store(false, Ordering::SeqCst);
            }
        }
        
        /// 添加数据 / Add data
        pub fn add_data(&self, item: String) {
            let mut data = self.data.lock().unwrap();
            data.push(item);
        }
        
        /// 获取统计信息 / Get statistics
        pub fn get_statistics(&self) -> (usize, usize, usize) {
            let data_count = self.data.lock().unwrap().len();
            let active_count = self.active_count.load(Ordering::SeqCst);
            let total_processed = self.total_processed.load(Ordering::SeqCst);
            (data_count, active_count, total_processed)
        }
    }

    /// 原子所有权操作示例 / Atomic Ownership Operations Example
    pub fn atomic_ownership_operations_example() {
        println!("=== 原子所有权操作示例 / Atomic Ownership Operations Example ===");
        
        let manager = Arc::new(AtomicOwnershipManager::new());
        let mut handles = vec![];
        
        // 创建多个工作线程 / Create multiple worker threads
        for i in 0..5 {
            let manager_clone = Arc::clone(&manager);
            let handle = thread::spawn(move || {
                for j in 0..3 {
                    // 尝试开始处理 / Try to start processing
                    if manager_clone.start_processing() {
                        println!("Thread {} started processing batch {}", i, j);
                        
                        // 模拟处理工作 / Simulate processing work
                        thread::sleep(Duration::from_millis(100));
                        
                        // 添加处理结果 / Add processing result
                        manager_clone.add_data(format!("Thread-{}-Batch-{}", i, j));
                        
                        // 结束处理 / End processing
                        manager_clone.end_processing();
                        println!("Thread {} finished processing batch {}", i, j);
                    } else {
                        println!("Thread {} could not start processing batch {}", i, j);
                    }
                }
            });
            handles.push(handle);
        }
        
        // 创建监控线程 / Create monitoring thread
        let manager_clone = Arc::clone(&manager);
        let monitor_handle = thread::spawn(move || {
            for _ in 0..20 {
                let (data_count, active_count, total_processed) = manager_clone.get_statistics();
                println!("Monitor: data={}, active={}, processed={}", 
                        data_count, active_count, total_processed);
                thread::sleep(Duration::from_millis(50));
            }
        });
        
        // 等待所有线程完成 / Wait for all threads to complete
        for handle in handles {
            handle.join().unwrap();
        }
        monitor_handle.join().unwrap();
        
        // 显示最终统计信息 / Show final statistics
        let (final_data_count, final_active_count, final_total_processed) = manager.get_statistics();
        println!("Final statistics: data={}, active={}, processed={}", 
                final_data_count, final_active_count, final_total_processed);
    }
}

/// # 4. 高级作用域管理 / Advanced Scope Management

/// ## 4.1 动态作用域 / Dynamic Scope
/// 
/// 演示如何实现动态作用域管理
/// Demonstrates how to implement dynamic scope management

pub mod dynamic_scope {
    use super::*;

    /// 作用域类型 / Scope Type
    #[derive(Debug, Clone)]
    pub enum ScopeType {
        Global,
        Function,
        Block,
        Loop,
        Conditional,
    }

    /// 作用域信息 / Scope Information
    #[derive(Debug, Clone)]
    pub struct ScopeInfo {
        pub id: u32,
        pub name: String,
        pub scope_type: ScopeType,
        pub variables: HashMap<String, String>,
        pub parent_id: Option<u32>,
        pub children: Vec<u32>,
    }

    impl ScopeInfo {
        /// 创建新的作用域信息 / Create new scope info
        pub fn new(id: u32, name: String, scope_type: ScopeType) -> Self {
            Self {
                id,
                name,
                scope_type,
                variables: HashMap::new(),
                parent_id: None,
                children: Vec::new(),
            }
        }
        
        /// 添加变量 / Add variable
        pub fn add_variable(&mut self, name: String, value: String) {
            self.variables.insert(name, value);
        }
        
        /// 获取变量 / Get variable
        pub fn get_variable(&self, name: &str) -> Option<&str> {
            self.variables.get(name).map(|s| s.as_str())
        }
        
        /// 添加子作用域 / Add child scope
        pub fn add_child(&mut self, child_id: u32) {
            self.children.push(child_id);
        }
    }

    /// 动态作用域管理器 / Dynamic Scope Manager
    pub struct DynamicScopeManager {
        pub scopes: HashMap<u32, ScopeInfo>,
        pub scope_stack: Vec<u32>,
        pub next_scope_id: u32,
    }

    impl DynamicScopeManager {
        /// 创建新的动态作用域管理器 / Create new dynamic scope manager
        pub fn new() -> Self {
            let mut manager = Self {
                scopes: HashMap::new(),
                scope_stack: Vec::new(),
                next_scope_id: 1,
            };
            
            // 创建全局作用域 / Create global scope
            let global_scope = ScopeInfo::new(0, "global".to_string(), ScopeType::Global);
            manager.scopes.insert(0, global_scope);
            manager.scope_stack.push(0);
            
            manager
        }
        
        /// 进入作用域 / Enter scope
        pub fn enter_scope(&mut self, name: String, scope_type: ScopeType) -> u32 {
            let scope_id = self.next_scope_id;
            self.next_scope_id += 1;
            
            let mut scope_info = ScopeInfo::new(scope_id, name, scope_type);
            
            // 设置父作用域 / Set parent scope
            if let Some(&parent_id) = self.scope_stack.last() {
                scope_info.parent_id = Some(parent_id);
                
                // 添加子作用域到父作用域 / Add child scope to parent scope
                if let Some(parent_scope) = self.scopes.get_mut(&parent_id) {
                    parent_scope.add_child(scope_id);
                }
            }
            
            self.scopes.insert(scope_id, scope_info);
            self.scope_stack.push(scope_id);
            
            scope_id
        }
        
        /// 退出作用域 / Exit scope
        pub fn exit_scope(&mut self) -> Option<u32> {
            self.scope_stack.pop()
        }
        
        /// 获取当前作用域 / Get current scope
        pub fn get_current_scope(&self) -> Option<&ScopeInfo> {
            self.scope_stack.last().and_then(|&id| self.scopes.get(&id))
        }
        
        /// 在当前作用域中添加变量 / Add variable to current scope
        pub fn add_variable(&mut self, name: String, value: String) -> Result<(), String> {
            if let Some(&current_id) = self.scope_stack.last() {
                if let Some(scope) = self.scopes.get_mut(&current_id) {
                    scope.add_variable(name, value);
                    Ok(())
                } else {
                    Err("Current scope not found".to_string())
                }
            } else {
                Err("No active scope".to_string())
            }
        }
        
        /// 查找变量 / Find variable
        pub fn find_variable(&self, name: &str) -> Option<(u32, String)> {
            // 从当前作用域开始向上查找 / Start from current scope and search upward
            for &scope_id in self.scope_stack.iter().rev() {
                if let Some(scope) = self.scopes.get(&scope_id) {
                    if let Some(value) = scope.variables.get(name) {
                        return Some((scope_id, value.clone()));
                    }
                }
            }
            None
        }
        
        /// 打印作用域树 / Print scope tree
        pub fn print_scope_tree(&self) {
            println!("=== 作用域树 / Scope Tree ===");
            self.print_scope_recursive(0, 0);
        }
        
        /// 递归打印作用域 / Print scope recursively
        fn print_scope_recursive(&self, scope_id: u32, depth: usize) {
            if let Some(scope) = self.scopes.get(&scope_id) {
                let indent = "  ".repeat(depth);
                println!("{}{} (ID: {}, Type: {:?})", 
                        indent, scope.name, scope.id, scope.scope_type);
                
                for &child_id in &scope.children {
                    self.print_scope_recursive(child_id, depth + 1);
                }
            }
        }
    }

    /// 动态作用域示例 / Dynamic Scope Example
    pub fn dynamic_scope_example() {
        println!("=== 动态作用域示例 / Dynamic Scope Example ===");
        
        let mut manager = DynamicScopeManager::new();
        
        // 添加全局变量 / Add global variables
        manager.add_variable("global_var".to_string(), "global_value".to_string()).unwrap();
        manager.add_variable("config".to_string(), "production".to_string()).unwrap();
        
        // 进入函数作用域 / Enter function scope
        let _function_id = manager.enter_scope("main_function".to_string(), ScopeType::Function);
        manager.add_variable("function_var".to_string(), "function_value".to_string()).unwrap();
        
        // 进入块作用域 / Enter block scope
        let _block_id = manager.enter_scope("if_block".to_string(), ScopeType::Block);
        manager.add_variable("block_var".to_string(), "block_value".to_string()).unwrap();
        
        // 进入循环作用域 / Enter loop scope
        let _loop_id = manager.enter_scope("for_loop".to_string(), ScopeType::Loop);
        manager.add_variable("loop_var".to_string(), "loop_value".to_string()).unwrap();
        
        // 查找变量 / Find variables
        println!("Looking for variables:");
        if let Some((scope_id, value)) = manager.find_variable("global_var") {
            println!("Found global_var in scope {}: {}", scope_id, value);
        }
        
        if let Some((scope_id, value)) = manager.find_variable("function_var") {
            println!("Found function_var in scope {}: {}", scope_id, value);
        }
        
        if let Some((scope_id, value)) = manager.find_variable("block_var") {
            println!("Found block_var in scope {}: {}", scope_id, value);
        }
        
        if let Some((scope_id, value)) = manager.find_variable("loop_var") {
            println!("Found loop_var in scope {}: {}", scope_id, value);
        }
        
        // 退出作用域 / Exit scopes
        manager.exit_scope(); // 退出循环作用域 / Exit loop scope
        manager.exit_scope(); // 退出块作用域 / Exit block scope
        manager.exit_scope(); // 退出函数作用域 / Exit function scope
        
        // 打印作用域树 / Print scope tree
        manager.print_scope_tree();
    }
}

/// 主函数 / Main Function
fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 高级所有权和借用示例 / Advanced Ownership and Borrowing Examples ===");
    
    // 1. 复杂所有权模式 / Complex Ownership Patterns
    ownership_transfer_chain::ownership_transfer_chain_example();
    ownership_sharing_patterns::ownership_sharing_patterns_example();
    
    // 2. 高级借用技巧 / Advanced Borrowing Techniques
    complex_borrowing_patterns::complex_borrowing_patterns_example();
    borrow_lifetime_management::borrow_lifetime_management_example();
    
    // 3. 并发所有权模式 / Concurrent Ownership Patterns
    inter_thread_ownership_sharing::inter_thread_ownership_sharing_example();
    atomic_ownership_operations::atomic_ownership_operations_example();
    
    // 4. 高级作用域管理 / Advanced Scope Management
    dynamic_scope::dynamic_scope_example();
    
    println!("\n=== 所有高级示例运行完成 / All Advanced Examples Completed ===");
    
    Ok(())
}
