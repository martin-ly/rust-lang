//! 测试夹具
//! 
//! 提供测试中使用的测试数据和夹具

/// 测试数据结构
pub struct TestData {
    pub id: usize,
    pub name: String,
    pub value: i32,
}

impl TestData {
    pub fn new(id: usize, name: &str, value: i32) -> Self {
        Self {
            id,
            name: name.to_string(),
            value,
        }
    }
}

/// 创建测试数据
pub fn create_test_data() -> Vec<TestData> {
    vec![
        TestData::new(1, "test1", 100),
        TestData::new(2, "test2", 200),
        TestData::new(3, "test3", 300),
    ]
}

/// 创建大量测试数据
pub fn create_large_test_data(count: usize) -> Vec<TestData> {
    (0..count)
        .map(|i| TestData::new(i, &format!("test_{}", i), i as i32))
        .collect()
}

/// 字符串测试数据
pub fn create_string_test_data() -> Vec<String> {
    vec![
        "hello".to_string(),
        "world".to_string(),
        "rust".to_string(),
        "testing".to_string(),
    ]
}

/// 数值测试数据
pub fn create_numeric_test_data() -> Vec<i32> {
    vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
}

/// 浮点数测试数据
pub fn create_float_test_data() -> Vec<f64> {
    vec![1.1, 2.2, 3.3, 4.4, 5.5]
}

/// 复杂嵌套结构测试数据
pub struct ComplexTestData {
    pub items: Vec<TestData>,
    pub metadata: std::collections::HashMap<String, String>,
    pub timestamp: std::time::SystemTime,
}

impl ComplexTestData {
    pub fn new() -> Self {
        let mut metadata = std::collections::HashMap::new();
        metadata.insert("version".to_string(), "1.0".to_string());
        metadata.insert("author".to_string(), "test".to_string());
        
        Self {
            items: create_test_data(),
            metadata,
            timestamp: std::time::SystemTime::now(),
        }
    }
}

/// 异步测试数据
pub struct AsyncTestData {
    pub delay_ms: u64,
    pub payload: String,
}

impl AsyncTestData {
    pub fn new(delay_ms: u64, payload: &str) -> Self {
        Self {
            delay_ms,
            payload: payload.to_string(),
        }
    }
}

/// 创建异步测试数据
pub fn create_async_test_data() -> Vec<AsyncTestData> {
    vec![
        AsyncTestData::new(10, "fast"),
        AsyncTestData::new(50, "medium"),
        AsyncTestData::new(100, "slow"),
    ]
}

/// 错误测试数据
pub fn create_error_test_data() -> Vec<Result<String, String>> {
    vec![
        Ok("success1".to_string()),
        Err("error1".to_string()),
        Ok("success2".to_string()),
        Err("error2".to_string()),
    ]
}

/// 性能测试数据
pub struct PerformanceTestData {
    pub size: usize,
    pub data: Vec<u8>,
}

impl PerformanceTestData {
    pub fn new(size: usize) -> Self {
        Self {
            size,
            data: vec![0u8; size],
        }
    }
}

/// 创建性能测试数据
pub fn create_performance_test_data(sizes: &[usize]) -> Vec<PerformanceTestData> {
    sizes.iter().map(|&size| PerformanceTestData::new(size)).collect()
}
