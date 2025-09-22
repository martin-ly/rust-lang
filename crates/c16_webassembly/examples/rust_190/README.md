# Rust 1.90 新特性在WebAssembly中的应用

## Rust 1.90 主要新特性

### 1. 常量泛型推断
- **功能**: 使用 `_` 让编译器自动推断常量泛型参数
- **应用场景**: 简化数组创建和类型推导

### 2. 生命周期语法检查
- **功能**: 改进的生命周期语法检查和错误提示
- **应用场景**: 提高代码质量和开发体验

### 3. FFI改进
- **功能**: 支持 `i128` 和 `u128` 类型在 `extern "C"` 函数中使用
- **应用场景**: 增强与C/C++的互操作性

### 4. 跨平台文档测试
- **功能**: 支持针对特定平台的文档测试
- **应用场景**: 提高文档的准确性和完整性

### 5. API稳定化
- **功能**: `Result::flatten` 和文件锁相关API稳定化
- **应用场景**: 简化错误处理和文件操作

## WebAssembly应用示例

### 1. 常量泛型推断示例

```rust
use wasm_bindgen::prelude::*;

// Rust 1.90 新特性：常量泛型推断
pub fn create_wasm_array<const LEN: usize>() -> [Value; LEN] {
    [Value::I32(0); _] // 编译器自动推断 LEN
}

#[wasm_bindgen]
pub struct WasmArrayBuilder<const SIZE: usize> {
    data: [u8; SIZE],
    position: usize,
}

#[wasm_bindgen]
impl<const SIZE: usize> WasmArrayBuilder<SIZE> {
    #[wasm_bindgen(constructor)]
    pub fn new() -> WasmArrayBuilder<SIZE> {
        WasmArrayBuilder {
            data: [0u8; _], // 编译器自动推断 SIZE
            position: 0,
        }
    }
    
    #[wasm_bindgen]
    pub fn push(&mut self, value: u8) -> Result<(), JsValue> {
        if self.position >= SIZE {
            return Err(JsValue::from_str("Array is full"));
        }
        
        self.data[self.position] = value;
        self.position += 1;
        Ok(())
    }
    
    #[wasm_bindgen]
    pub fn get(&self, index: usize) -> Result<u8, JsValue> {
        if index >= self.position {
            return Err(JsValue::from_str("Index out of bounds"));
        }
        
        Ok(self.data[index])
    }
}

// 使用示例
#[wasm_bindgen]
pub fn create_buffers() -> JsValue {
    let buffer_1k: WasmArrayBuilder<1024> = WasmArrayBuilder::new();
    let buffer_4k: WasmArrayBuilder<4096> = WasmArrayBuilder::new();
    
    // 返回创建的对象
    JsValue::from_serde(&(buffer_1k, buffer_4k)).unwrap()
}
```

### 2. 生命周期语法检查示例

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct WebAssemblyModule<'a> {
    name: &'a str,
    data: Vec<u8>,
}

// Rust 1.90 新特性：生命周期语法检查
impl<'a> WebAssemblyModule<'a> {
    pub fn process_module<'b>(&'b self) -> &'_ WebAssemblyModule<'b> {
        // 编译器建议显式使用 '_' 标示生命周期
        self
    }
    
    pub fn validate_module(&self) -> Result<(), ModuleError> {
        if self.data.is_empty() {
            return Err(ModuleError::EmptyModule);
        }
        
        // 验证WebAssembly魔数
        if self.data.len() < 4 || &self.data[0..4] != b"\x00asm" {
            return Err(ModuleError::InvalidMagic);
        }
        
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ModuleError {
    #[error("Empty module")]
    EmptyModule,
    #[error("Invalid magic number")]
    InvalidMagic,
}

#[wasm_bindgen]
impl<'a> WebAssemblyModule<'a> {
    #[wasm_bindgen(constructor)]
    pub fn new(name: &'a str, data: &[u8]) -> WebAssemblyModule<'a> {
        WebAssemblyModule {
            name,
            data: data.to_vec(),
        }
    }
    
    #[wasm_bindgen]
    pub fn get_name(&self) -> &str {
        self.name
    }
    
    #[wasm_bindgen]
    pub fn get_size(&self) -> usize {
        self.data.len()
    }
}
```

### 3. FFI改进示例（128位整数支持）

```rust
use wasm_bindgen::prelude::*;

// Rust 1.90 新特性：128位整数 FFI 支持
extern "C" {
    fn wasm_i128_operation(value: i128) -> i128;
    fn wasm_u128_operation(value: u128) -> u128;
    fn wasm_128bit_add(a: i128, b: i128) -> i128;
    fn wasm_128bit_multiply(a: u128, b: u128) -> u128;
}

#[wasm_bindgen]
pub struct BigIntCalculator;

#[wasm_bindgen]
impl BigIntCalculator {
    #[wasm_bindgen(constructor)]
    pub fn new() -> BigIntCalculator {
        BigIntCalculator
    }
    
    // 在 WebAssembly 中使用 128 位整数
    #[wasm_bindgen]
    pub fn calculate_large_numbers(&self) -> JsValue {
        unsafe {
            let i128_result = wasm_i128_operation(123456789012345678901234567890i128);
            let u128_result = wasm_u128_operation(987654321098765432109876543210u128);
            let add_result = wasm_128bit_add(1000000000000000000i128, 2000000000000000000i128);
            let mul_result = wasm_128bit_multiply(1000000000000000000u128, 2000000000000000000u128);
            
            let results = BigIntResults {
                i128_result,
                u128_result,
                add_result,
                mul_result,
            };
            
            JsValue::from_serde(&results).unwrap()
        }
    }
    
    #[wasm_bindgen]
    pub fn safe_128bit_operation(&self, a: &str, b: &str) -> Result<JsValue, JsValue> {
        let a_parsed: i128 = a.parse().map_err(|e| JsValue::from_str(&e.to_string()))?;
        let b_parsed: i128 = b.parse().map_err(|e| JsValue::from_str(&e.to_string()))?;
        
        // 检查溢出
        let result = a_parsed.checked_add(b_parsed)
            .ok_or_else(|| JsValue::from_str("Integer overflow"))?;
        
        Ok(JsValue::from_str(&result.to_string()))
    }
}

#[derive(serde::Serialize)]
struct BigIntResults {
    i128_result: i128,
    u128_result: u128,
    add_result: i128,
    mul_result: u128,
}
```

### 4. Result::flatten 示例

```rust
use wasm_bindgen::prelude::*;

// Rust 1.90 新特性：Result::flatten
#[wasm_bindgen]
pub struct WebAssemblyValidator;

#[wasm_bindgen]
impl WebAssemblyValidator {
    #[wasm_bindgen(constructor)]
    pub fn new() -> WebAssemblyValidator {
        WebAssemblyValidator
    }
    
    #[wasm_bindgen]
    pub fn validate_module(&self, data: &[u8]) -> Result<JsValue, JsValue> {
        // 使用 Result::flatten 简化嵌套的 Result 处理
        let validation_result = self.parse_module(data)
            .flatten() // 自动处理 Result<Result<T, E>, E>
            .map_err(|e| JsValue::from_str(&e.to_string()))?;
        
        Ok(JsValue::from_serde(&validation_result).unwrap())
    }
    
    fn parse_module(&self, data: &[u8]) -> Result<Result<ModuleInfo, ValidationError>, ValidationError> {
        if data.is_empty() {
            return Ok(Err(ValidationError::EmptyData));
        }
        
        // 模拟解析过程
        let module_info = ModuleInfo {
            size: data.len(),
            magic: data[0..4].to_vec(),
            version: 1,
        };
        
        Ok(Ok(module_info))
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ValidationError {
    #[error("Empty data")]
    EmptyData,
    #[error("Invalid format")]
    InvalidFormat,
    #[error("Unsupported version")]
    UnsupportedVersion,
}

#[derive(serde::Serialize)]
struct ModuleInfo {
    size: usize,
    magic: Vec<u8>,
    version: u32,
}
```

### 5. 跨平台文档测试示例

```rust
use wasm_bindgen::prelude::*;

/// WebAssembly 内存管理器
/// 
/// # 示例
/// 
/// ```rust
/// # use wasm_bindgen::prelude::*;
/// let mut manager = MemoryManager::new(1024);
/// manager.allocate(256);
/// ```
/// 
/// # 平台特定示例
/// 
/// ```rust,no_run
/// # #[cfg(target_arch = "wasm32")]
/// # {
/// # use wasm_bindgen::prelude::*;
/// let manager = MemoryManager::new(1024);
/// // WebAssembly 特定代码
/// # }
/// ```
#[wasm_bindgen]
pub struct MemoryManager {
    memory: Vec<u8>,
    allocated: Vec<bool>,
}

#[wasm_bindgen]
impl MemoryManager {
    /// 创建新的内存管理器
    /// 
    /// # 参数
    /// 
    /// * `size` - 内存大小（字节）
    /// 
    /// # 示例
    /// 
    /// ```rust
    /// # use wasm_bindgen::prelude::*;
    /// let manager = MemoryManager::new(1024);
    /// assert_eq!(manager.get_size(), 1024);
    /// ```
    #[wasm_bindgen(constructor)]
    pub fn new(size: usize) -> MemoryManager {
        MemoryManager {
            memory: vec![0u8; size],
            allocated: vec![false; size],
        }
    }
    
    /// 分配内存块
    /// 
    /// # 参数
    /// 
    /// * `size` - 要分配的大小
    /// 
    /// # 返回值
    /// 
    /// 返回分配的内存地址，如果分配失败返回 -1
    /// 
    /// # 示例
    /// 
    /// ```rust
    /// # use wasm_bindgen::prelude::*;
    /// let mut manager = MemoryManager::new(1024);
    /// let addr = manager.allocate(256);
    /// assert!(addr >= 0);
    /// ```
    #[wasm_bindgen]
    pub fn allocate(&mut self, size: usize) -> i32 {
        for i in 0..=(self.memory.len() - size) {
            if !self.allocated[i..i + size].iter().any(|&allocated| allocated) {
                for j in i..i + size {
                    self.allocated[j] = true;
                }
                return i as i32;
            }
        }
        -1
    }
    
    /// 释放内存块
    /// 
    /// # 参数
    /// 
    /// * `addr` - 要释放的内存地址
    /// * `size` - 要释放的大小
    /// 
    /// # 示例
    /// 
    /// ```rust
    /// # use wasm_bindgen::prelude::*;
    /// let mut manager = MemoryManager::new(1024);
    /// let addr = manager.allocate(256);
    /// manager.deallocate(addr, 256);
    /// ```
    #[wasm_bindgen]
    pub fn deallocate(&mut self, addr: i32, size: usize) {
        if addr >= 0 && (addr as usize) + size <= self.memory.len() {
            for i in (addr as usize)..(addr as usize) + size {
                self.allocated[i] = false;
            }
        }
    }
    
    /// 获取内存大小
    /// 
    /// # 示例
    /// 
    /// ```rust
    /// # use wasm_bindgen::prelude::*;
    /// let manager = MemoryManager::new(1024);
    /// assert_eq!(manager.get_size(), 1024);
    /// ```
    #[wasm_bindgen]
    pub fn get_size(&self) -> usize {
        self.memory.len()
    }
}
```

## 综合应用示例

### Rust 1.90 + WebAssembly 2.0 集成

```rust
use wasm_bindgen::prelude::*;
use serde::{Serialize, Deserialize};

/// Rust 1.90 与 WebAssembly 2.0 的综合集成示例
#[wasm_bindgen]
pub struct Rust190Wasm2Integration {
    bulk_memory_manager: BulkMemoryManager,
    tail_call_optimizer: TailCallOptimizer,
    host_binding_manager: HostBindingManager,
}

#[wasm_bindgen]
impl Rust190Wasm2Integration {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Rust190Wasm2Integration {
        Rust190Wasm2Integration {
            bulk_memory_manager: BulkMemoryManager::new(1024 * 1024), // 1MB
            tail_call_optimizer: TailCallOptimizer::new(),
            host_binding_manager: HostBindingManager::new(),
        }
    }
    
    /// 运行综合测试
    #[wasm_bindgen]
    pub fn run_comprehensive_test(&mut self) -> Result<JsValue, JsValue> {
        let mut test_result = TestResult::new();
        
        // 测试批量内存操作
        if let Err(e) = self.bulk_memory_manager.bulk_copy(0, 100, 50) {
            test_result.add_error(format!("批量内存复制失败: {}", e));
        } else {
            test_result.add_success("批量内存复制成功".to_string());
        }
        
        // 测试尾调用优化
        let args = vec![Value::I32(42)];
        if let Err(e) = self.tail_call_optimizer.execute_tail_call(0, args) {
            test_result.add_error(format!("尾调用优化失败: {}", e));
        } else {
            test_result.add_success("尾调用优化成功".to_string());
        }
        
        // 测试宿主绑定
        let js_args = vec![Value::String("Hello from Rust!".to_string())];
        if let Err(e) = self.host_binding_manager.call_javascript_function("console.log", js_args) {
            test_result.add_error(format!("宿主绑定失败: {}", e));
        } else {
            test_result.add_success("宿主绑定成功".to_string());
        }
        
        Ok(JsValue::from_serde(&test_result).unwrap())
    }
}

// 支持结构体
#[derive(Serialize, Deserialize)]
struct TestResult {
    successes: Vec<String>,
    errors: Vec<String>,
}

impl TestResult {
    fn new() -> Self {
        Self {
            successes: Vec::new(),
            errors: Vec::new(),
        }
    }
    
    fn add_success(&mut self, message: String) {
        self.successes.push(message);
    }
    
    fn add_error(&mut self, message: String) {
        self.errors.push(message);
    }
}

// 简化的支持结构体
struct BulkMemoryManager {
    memory: Vec<u8>,
}

impl BulkMemoryManager {
    fn new(size: usize) -> Self {
        Self {
            memory: vec![0u8; size],
        }
    }
    
    fn bulk_copy(&mut self, src: u32, dst: u32, size: u32) -> Result<(), String> {
        if (src + size) as usize > self.memory.len() || (dst + size) as usize > self.memory.len() {
            return Err("Memory bounds exceeded".to_string());
        }
        
        self.memory.copy_within(src as usize..(src + size) as usize, dst as usize);
        Ok(())
    }
}

struct TailCallOptimizer {
    call_stack: Vec<TailCall>,
}

impl TailCallOptimizer {
    fn new() -> Self {
        Self {
            call_stack: Vec::new(),
        }
    }
    
    fn execute_tail_call(&mut self, target: u32, args: Vec<Value>) -> Result<Value, String> {
        if self.call_stack.len() > 0 {
            self.call_stack.pop();
        }
        
        let tail_call = TailCall { target, args };
        self.call_stack.push(tail_call);
        
        Ok(Value::I32(42))
    }
}

struct HostBindingManager {
    bindings: std::collections::HashMap<String, HostBinding>,
}

impl HostBindingManager {
    fn new() -> Self {
        Self {
            bindings: std::collections::HashMap::new(),
        }
    }
    
    fn call_javascript_function(&self, name: &str, args: Vec<Value>) -> Result<Value, String> {
        if let Some(_binding) = self.bindings.get(name) {
            Ok(Value::String(format!("JS函数 {} 被调用", name)))
        } else {
            Err("Function not found".to_string())
        }
    }
}

#[derive(Debug, Clone)]
enum Value {
    I32(i32),
    String(String),
}

struct TailCall {
    target: u32,
    args: Vec<Value>,
}

struct HostBinding {
    binding_type: HostBindingType,
}

enum HostBindingType {
    JavaScriptFunction,
}
```

## 最佳实践

### 1. 使用常量泛型推断
- 在创建固定大小数组时使用 `_` 让编译器推断
- 简化类型声明，提高代码可读性

### 2. 利用生命周期语法检查
- 使用 `'_` 明确标示生命周期
- 提高代码质量和编译器错误提示

### 3. 安全使用128位整数
- 在FFI中安全使用 `i128` 和 `u128`
- 注意溢出检查和边界条件

### 4. 使用Result::flatten
- 简化嵌套Result的处理
- 提高错误处理的清晰度

### 5. 编写平台特定文档
- 使用条件编译编写平台特定示例
- 提高文档的准确性和完整性

## 总结

Rust 1.90的新特性为WebAssembly开发带来了更好的开发体验和更强的功能支持。通过合理使用这些新特性，可以编写更安全、更高效的WebAssembly代码。
