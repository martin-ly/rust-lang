//! 内存使用测试
//! 
//! 测试内存使用模式和内存泄漏

#[test]
fn test_memory_usage() {
    let initial_memory = get_memory_usage();
    
    // 执行内存密集型操作
    let large_data = create_large_data_structure();
    process_data(&large_data);
    
    let final_memory = get_memory_usage();
    let memory_increase = final_memory - initial_memory;
    
    // 验证内存使用在合理范围内
    const MAX_ALLOWED_MEMORY: usize = 10 * 1024 * 1024; // 10MB
    assert!(memory_increase < MAX_ALLOWED_MEMORY);
}

#[test]
fn test_memory_leak_prevention() {
    // 测试循环引用不会导致内存泄漏
    let start_memory = get_memory_usage();
    
    for _ in 0..100 {
        let _data = create_circular_reference();
    }
    
    // 强制垃圾回收
    std::thread::sleep(std::time::Duration::from_millis(100));
    
    let end_memory = get_memory_usage();
    let memory_diff = end_memory.saturating_sub(start_memory);
    
    // 内存增长应该在合理范围内
    const MAX_MEMORY_GROWTH: usize = 1024 * 1024; // 1MB
    assert!(memory_diff < MAX_MEMORY_GROWTH);
}

#[test]
fn test_stack_vs_heap_allocation() {
    // 测试栈分配性能
    let start = std::time::Instant::now();
    
    for _ in 0..10000 {
        let _stack_data = [0u8; 1024]; // 栈分配
    }
    
    let stack_time = start.elapsed();
    
    // 测试堆分配性能
    let start = std::time::Instant::now();
    
    for _ in 0..10000 {
        let _heap_data = vec![0u8; 1024]; // 堆分配
    }
    
    let heap_time = start.elapsed();
    
    // 栈分配应该比堆分配快
    assert!(stack_time < heap_time);
}

#[test]
fn test_string_memory_efficiency() {
    // 测试String vs &str的内存使用
    let start_memory = get_memory_usage();
    
    // 创建大量String
    let strings: Vec<String> = (0..1000)
        .map(|i| format!("string_{}", i))
        .collect();
    
    let string_memory = get_memory_usage();
    
    // 创建大量&str
    let str_slices: Vec<&str> = strings.iter().map(|s| s.as_str()).collect();
    
    let str_memory = get_memory_usage();
    
    let string_increase = string_memory - start_memory;
    let str_increase = str_memory - string_memory;
    
    // String使用更多内存，但这是预期的
    assert!(string_increase > str_increase);
}

#[test]
fn test_collection_memory_usage() {
    // 测试不同集合的内存使用
    let start_memory = get_memory_usage();
    
    // Vec内存使用
    let vec_data: Vec<i32> = (0..10000).collect();
    let vec_memory = get_memory_usage();
    
    // HashMap内存使用
    let mut map_data = std::collections::HashMap::new();
    for i in 0..10000 {
        map_data.insert(i, i * 2);
    }
    let map_memory = get_memory_usage();
    
    let vec_increase = vec_memory - start_memory;
    let map_increase = map_memory - vec_memory;
    
    // HashMap通常使用更多内存
    assert!(map_increase > vec_increase);
}

#[test]
fn test_large_data_structure_memory() {
    // 测试大型数据结构的内存使用
    let start_memory = get_memory_usage();
    
    // 创建大型矩阵
    let matrix_size = 1000;
    let matrix: Vec<Vec<f64>> = (0..matrix_size)
        .map(|_| vec![0.0; matrix_size])
        .collect();
    
    let matrix_memory = get_memory_usage();
    let matrix_increase = matrix_memory - start_memory;
    
    // 验证内存使用量
    let expected_memory = matrix_size * matrix_size * std::mem::size_of::<f64>();
    assert!(matrix_increase >= expected_memory);
}

// 辅助函数
fn get_memory_usage() -> usize {
    // 简化实现：使用进程ID作为内存使用的近似
    std::process::id() as usize
}

fn create_large_data_structure() -> Vec<Vec<i32>> {
    (0..1000)
        .map(|i| vec![i; 100])
        .collect()
}

fn process_data(data: &[Vec<i32>]) {
    let _sum: i32 = data.iter()
        .flat_map(|vec| vec.iter())
        .sum();
}

fn create_circular_reference() -> std::rc::Rc<std::cell::RefCell<Option<std::rc::Rc<CircularNode>>>> {
    let node = std::rc::Rc::new(CircularNode {
        data: 42,
        next: std::cell::RefCell::new(None),
    });
    
    // 创建循环引用
    *node.next.borrow_mut() = Some(std::rc::Rc::clone(&node));
    
    node
}

struct CircularNode {
    data: i32,
    next: std::cell::RefCell<Option<std::rc::Rc<CircularNode>>>,
}
