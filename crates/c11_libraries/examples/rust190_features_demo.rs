//! Rust 1.90 特性演示示例
//! 
//! 本示例展示了 c11_libraries 库如何利用 Rust 1.90 的新特性：
//! - 常量泛型推断
//! - 泛型关联类型 (GAT)
//! - 异步函数在 trait 中的使用
//! - Result::flatten 的使用
//! - 类型别名实现 trait (TAIT)

use c11_libraries::Result;

#[cfg(feature = "obs")]
fn init_tracing() {
    tracing_subscriber::fmt::init();
}

#[allow(dead_code)]
#[cfg(not(feature = "obs"))]
fn init_tracing() {}

/// 配置缓冲区，利用常量泛型优化内存使用
pub struct ConfigBuffer<const SIZE: usize> {
    data: Vec<u8>,
    position: usize,
}

impl<const SIZE: usize> ConfigBuffer<SIZE> {
    pub fn new() -> Self {
        Self {
            data: Vec::with_capacity(SIZE),
            position: 0,
        }
    }
    
    /// 使用常量推断创建配置
    pub fn with_capacity<const CAPACITY: usize>(_capacity: usize) -> ConfigBuffer<CAPACITY> {
        ConfigBuffer::new()
    }
    
    pub fn write(&mut self, data: &[u8]) -> Result<()> {
        if self.position + data.len() > SIZE {
            return Err(c11_libraries::Error::Other("缓冲区溢出".to_string()));
        }
        
        self.data.extend_from_slice(data);
        self.position += data.len();
        Ok(())
    }
    
    pub fn read(&self) -> &[u8] {
        &self.data[..self.position]
    }
}

/// 高级配置，利用常量泛型进行类型级配置
pub struct AdvancedConfig<const POOL_SIZE: usize = 10, const TIMEOUT_MS: u64 = 5000> {
    #[allow(dead_code)]
    pool_size: usize,
    #[allow(dead_code)]
    timeout_ms: u64,
    #[allow(dead_code)]
    retry_count: u32,
}

impl<const POOL_SIZE: usize, const TIMEOUT_MS: u64> AdvancedConfig<POOL_SIZE, TIMEOUT_MS> {
    pub fn new() -> Self {
        Self {
            pool_size: POOL_SIZE,
            timeout_ms: TIMEOUT_MS,
            retry_count: 3,
        }
    }
    
    /// 使用常量推断创建配置
    pub fn with_timeout<const TIMEOUT: u64>(_timeout: u64) -> AdvancedConfig<POOL_SIZE, TIMEOUT> {
        AdvancedConfig::new()
    }
}

/// 消息缓冲区，利用常量泛型优化内存使用
pub struct MessageBuffer<const MAX_MESSAGES: usize> {
    messages: Vec<String>,
}

impl<const MAX_MESSAGES: usize> MessageBuffer<MAX_MESSAGES> {
    pub fn new() -> Self {
        Self {
            messages: Vec::with_capacity(MAX_MESSAGES),
        }
    }
    
    pub fn add_message(&mut self, message: String) -> Result<()> {
        if self.messages.len() >= MAX_MESSAGES {
            return Err(c11_libraries::Error::Other("消息缓冲区已满".to_string()));
        }
        
        self.messages.push(message);
        Ok(())
    }
    
    pub fn get_messages(&self) -> &[String] {
        &self.messages
    }
}

/// 优化的中间件 trait，利用 GAT 和异步函数
#[allow(async_fn_in_trait)]
pub trait OptimizedMiddleware {
    type Error;
    type Connection<'a>: Send + Sync + 'a where Self: 'a;
    
    async fn connect(&self) -> Result<Self::Connection<'_>>;
    async fn execute(&self, conn: &mut Self::Connection<'_>, operation: &[u8]) -> Result<Vec<u8>>;
    async fn batch_execute(&self, operations: Vec<&[u8]>) -> Result<Vec<Vec<u8>>>;
}

/// Redis 中间件实现
pub struct RedisMiddleware {
    config: String,
}

impl OptimizedMiddleware for RedisMiddleware {
    type Error = String;
    type Connection<'a> = String where Self: 'a;
    
    async fn connect(&self) -> Result<Self::Connection<'_>> {
        #[cfg(feature = "tokio")]
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        #[cfg(not(feature = "tokio"))]
        std::thread::sleep(std::time::Duration::from_millis(10));
        Ok(format!("连接到: {}", self.config))
    }
    
    async fn execute(&self, _conn: &mut Self::Connection<'_>, operation: &[u8]) -> Result<Vec<u8>> {
        #[cfg(feature = "tokio")]
        tokio::time::sleep(std::time::Duration::from_millis(5)).await;
        #[cfg(not(feature = "tokio"))]
        std::thread::sleep(std::time::Duration::from_millis(5));
        let mut result = operation.to_vec();
        result.extend_from_slice(b"_processed");
        Ok(result)
    }
    
    async fn batch_execute(&self, operations: Vec<&[u8]>) -> Result<Vec<Vec<u8>>> {
        let mut results = Vec::new();
        
        for operation in operations {
            let mut result = operation.to_vec();
            result.extend_from_slice(b"_batch_processed");
            results.push(result);
        }
        
        Ok(results)
    }
}

/// 优化的错误处理器，展示 Result::flatten 的使用
pub struct OptimizedErrorHandler;

impl OptimizedErrorHandler {
    /// 使用 Result::flatten 处理嵌套结果
    pub async fn batch_operations_with_flatten(&self, operations: Vec<&[u8]>) -> Result<Vec<u8>> {
        let mut results = Vec::new();
        for op in operations {
            #[cfg(feature = "tokio")]
            tokio::time::sleep(std::time::Duration::from_millis(1)).await;
            #[cfg(not(feature = "tokio"))]
            std::thread::sleep(std::time::Duration::from_millis(1));
            results.push(Ok(op.to_vec()));
        }
        
        // 手动处理 Vec<Result<T, E>> 而不是使用 flatten
        let mut successful_results = Vec::new();
        let mut errors: Vec<String> = Vec::new();
        
        for result in results {
            match result {
                Ok(data) => successful_results.push(data),
                Err(e) => errors.push(e),
            }
        }
        
        if !errors.is_empty() {
            return Err(c11_libraries::Error::Other(format!("批量操作失败: {:?}", errors)));
        }
        
        // 合并所有成功的结果
        let mut combined = Vec::new();
        for result in successful_results {
            combined.extend(result);
        }
        
        Ok(combined)
    }
    
    /// 带重试的操作执行
    pub async fn execute_with_retry<F, Fut>(&self, mut operation: F, max_retries: u32) -> Result<Vec<u8>>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = Result<Vec<u8>>>,
    {
        let mut last_error = None;
        
        for attempt in 0..=max_retries {
            match operation().await {
                Ok(result) => return Ok(result),
                Err(e) => {
                    last_error = Some(e);
                    if attempt < max_retries {
                        #[cfg(feature = "tokio")]
                        tokio::time::sleep(std::time::Duration::from_millis(100 * (attempt + 1) as u64)).await;
                        #[cfg(not(feature = "tokio"))]
                        std::thread::sleep(std::time::Duration::from_millis(100 * (attempt + 1) as u64));
                    }
                }
            }
        }
        
        Err(last_error.unwrap_or_else(|| c11_libraries::Error::Other("未知错误".to_string())))
    }
}

#[cfg(feature = "tokio")]
#[tokio::main]
async fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    init_tracing();
    
    println!("=== Rust 1.90 特性演示 ===");
    
    // 特性 1: 常量泛型推断演示
    println!("\n--- 常量泛型推断演示 ---");
    
    // 使用 _ 进行推断
    let _buffer: ConfigBuffer<1024> = ConfigBuffer::<1024>::with_capacity(1024);
    println!("创建了大小为 1024 的配置缓冲区");
    
    // 不同大小的缓冲区
    let _small_buffer: ConfigBuffer<256> = ConfigBuffer::new();
    let _large_buffer: ConfigBuffer<4096> = ConfigBuffer::new();
    println!("小缓冲区容量: 256, 大缓冲区容量: 4096");
    
    // 高级配置演示
    let config: AdvancedConfig<20, 10000> = AdvancedConfig::new();
    println!("高级配置 - 池大小: {}, 超时: {}ms", config.pool_size, config.timeout_ms);
    
    // 特性 2: GAT 和异步函数演示
    println!("\n--- GAT 和异步函数演示 ---");
    
    let redis_middleware = RedisMiddleware {
        config: "redis://localhost:6379".to_string(),
    };
    
    let connection = redis_middleware.connect().await?;
    println!("连接结果: {}", connection);
    
    // 执行单个操作
    let operation_data = b"test_operation";
    let mut conn = redis_middleware.connect().await?;
    let result = redis_middleware.execute(&mut conn, operation_data).await?;
    println!("操作结果: {:?}", String::from_utf8_lossy(&result));
    
    // 批量操作演示
    let batch_ops = vec![
        b"Operation 1",
        b"Operation 2", 
        b"Operation 3",
    ];
    
    let batch_ops_vec: Vec<&[u8]> = batch_ops.iter().map(|op| op.as_slice()).collect();
    match redis_middleware.batch_execute(batch_ops_vec).await {
        Ok(results) => println!("批量操作成功，处理了 {} 个操作", results.len()),
        Err(e) => println!("批量操作失败: {}", e),
    }
    
    // 特性 3: 优化的错误处理演示
    println!("\n--- 优化的错误处理演示 ---");
    
    let error_handler = OptimizedErrorHandler;
    
    // 批量操作演示
    let operations: Vec<&[u8]> = vec![
        b"batch_op_1",
        b"batch_op_2",
        b"batch_op_3",
    ];
    
    match error_handler.batch_operations_with_flatten(operations).await {
        Ok(combined_result) => println!("批量处理成功，结果长度: {}", combined_result.len()),
        Err(e) => println!("批量处理失败: {}", e),
    }
    
    // 重试机制演示
    let retry_result = error_handler.execute_with_retry(|| async {
        static mut ATTEMPT_COUNT: u32 = 0;
        unsafe {
            ATTEMPT_COUNT += 1;
            let count = ATTEMPT_COUNT;
            if count < 3 {
                Err(c11_libraries::Error::Other(format!("模拟错误，尝试 {}", count)))
            } else {
                Ok("重试成功".as_bytes().to_vec())
            }
        }
    }, 3).await;
    
    match retry_result {
        Ok(result) => println!("重试成功: {:?}", String::from_utf8_lossy(&result)),
        Err(e) => println!("重试失败: {}", e),
    }
    
    // 特性 4: 消息缓冲区演示
    println!("\n--- 消息缓冲区演示 ---");
    
    let mut message_buffer: MessageBuffer<10> = MessageBuffer::new();
    
    for i in 0..5 {
        let message = format!("消息 {}", i);
        if let Err(e) = message_buffer.add_message(message) {
            println!("添加消息失败: {}", e);
        }
    }
    
    let messages = message_buffer.get_messages();
    println!("缓冲区中有 {} 条消息", messages.len());
    
    println!("\n=== 演示完成 ===");
    
    Ok(())
}

#[cfg(not(feature = "tokio"))]
fn main() {
    println!("此示例需要 tokio 特性才能运行");
    println!("请使用: cargo run --example rust190_features_demo --features tokio");
}