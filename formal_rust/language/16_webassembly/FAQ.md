# WebAssembly系统常见问题解答 (FAQ)

## 编译相关问题

### Q1: 如何将Rust代码编译为WebAssembly?

**A**: 使用wasm-pack工具可以将Rust代码编译为WebAssembly：

```bash
# 安装wasm-pack
cargo install wasm-pack

# 编译为WebAssembly
wasm-pack build --target web

# 编译为Node.js
wasm-pack build --target nodejs

# 编译为通用目标
wasm-pack build --target bundler
```

**理论映射**: 编译函数 $C: \text{Rust} \rightarrow \text{WebAssembly}$ 保持语义等价性。

### Q2: 编译时出现类型错误怎么办?

**A**: 检查Rust类型到WebAssembly类型的映射：

```rust
// 正确的类型映射
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

// 避免使用复杂类型
#[wasm_bindgen]
pub fn process_string(s: &str) -> String {
    s.to_uppercase()
}
```

**理论映射**: 类型映射函数 $\text{types}: \text{RustTypes} \rightarrow \text{WasmTypes}$ 必须保持类型安全。

### Q3: 如何处理编译优化问题?

**A**: 使用编译优化策略：

```rust
// 启用优化
[profile.release]
opt-level = 3
lto = true
codegen-units = 1

// 使用wasm-opt进行后处理优化
wasm-opt -O4 -o optimized.wasm input.wasm
```

**理论映射**: 优化函数 $\text{optimize}: \text{IR} \rightarrow \text{OptimizedIR}$ 保持语义等价性。

### Q4: 编译后的文件太大怎么办?

**A**: 使用多种优化策略：

```bash
# 启用代码压缩
wasm-pack build --release

# 使用wasm-opt进行优化
wasm-opt -Os -o small.wasm input.wasm

# 启用LTO优化
RUSTFLAGS="-C lto=fat" wasm-pack build
```

**理论映射**: 代码大小优化保持功能等价性 $\text{size\_optimize}(module) \equiv module$。

## 运行时问题

### Q5: WebAssembly运行时如何工作?

**A**: WebAssembly运行时提供执行环境：

```javascript
// 加载WebAssembly模块
const wasmModule = await WebAssembly.instantiateStreaming(
    fetch('module.wasm'),
    importObject
);

// 调用函数
const result = wasmModule.instance.exports.add(1, 2);
```

**理论映射**: 运行时环境 $\mathcal{R} = (\text{Engine}, \text{Memory}, \text{API})$ 提供执行支持。

### Q6: 如何处理内存管理问题?

**A**: WebAssembly使用线性内存模型：

```rust
#[wasm_bindgen]
pub fn allocate_memory(size: usize) -> *mut u8 {
    let mut memory = Vec::with_capacity(size);
    let ptr = memory.as_mut_ptr();
    std::mem::forget(memory);
    ptr
}

#[wasm_bindgen]
pub fn free_memory(ptr: *mut u8, size: usize) {
    unsafe {
        let _memory = Vec::from_raw_parts(ptr, size, size);
    }
}
```

**理论映射**: 线性内存 $\text{Memory} = \text{Array}[\text{Byte}]$ 提供连续地址空间。

### Q7: 如何实现异常处理?

**A**: WebAssembly支持异常处理：

```rust
#[wasm_bindgen]
pub fn safe_division(a: f64, b: f64) -> Result<f64, String> {
    if b == 0.0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}
```

**理论映射**: 异常处理保持程序安全 $\text{safe}(P) \Rightarrow \text{safe}(\text{handle\_exception}(P))$。

### Q8: 如何优化运行时性能?

**A**: 使用多种性能优化技术：

```rust
// 使用SIMD指令
#[target_feature(enable = "simd128")]
pub unsafe fn vector_add(a: &[f32], b: &[f32]) -> Vec<f32> {
    // SIMD实现
}

// 使用并行处理
#[wasm_bindgen]
pub fn parallel_process(data: &[u8]) -> Vec<u8> {
    // 并行处理实现
}
```

**理论映射**: 性能优化保持语义等价性 $\text{performance}(P_{\text{optimized}}) \geq \text{performance}(P_{\text{original}})$。

## 互操作问题

### Q9: 如何与JavaScript互操作?

**A**: 使用wasm-bindgen进行互操作：

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct Calculator {
    value: f64,
}

#[wasm_bindgen]
impl Calculator {
    pub fn new() -> Calculator {
        Calculator { value: 0.0 }
    }
    
    pub fn add(&mut self, x: f64) {
        self.value += x;
    }
    
    pub fn get_value(&self) -> f64 {
        self.value
    }
}
```

**理论映射**: 互操作函数 $\text{interop}: \text{WasmModule} \leftrightarrow \text{JavaScript}$ 保持类型安全。

### Q10: 如何实现系统接口调用?

**A**: 使用WASI或自定义宿主函数：

```rust
// 使用WASI
use std::fs;
use std::io::{Read, Write};

#[wasm_bindgen]
pub fn read_file(path: &str) -> Result<String, String> {
    let mut file = fs::File::open(path)
        .map_err(|e| e.to_string())?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)
        .map_err(|e| e.to_string())?;
    Ok(contents)
}
```

**理论映射**: 系统调用接口 $\text{Syscall}: \text{WasmModule} \times \text{HostAPI} \rightarrow \text{Result}$。

### Q11: 如何处理数据类型转换?

**A**: 实现类型转换机制：

```rust
#[wasm_bindgen]
pub fn convert_types() {
    // 数字类型转换
    let int_val: i32 = 42;
    let float_val: f64 = int_val as f64;
    
    // 字符串转换
    let string_val = "Hello, WASM!";
    let js_string = JsValue::from_str(string_val);
}
```

**理论映射**: 类型转换函数 $\text{convert}: \text{RustType} \rightarrow \text{WasmType}$ 保持类型安全。

### Q12: 如何实现回调机制?

**A**: 使用JavaScript回调函数：

```rust
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn process_with_callback(data: &[u8], callback: js_sys::Function) -> Result<(), JsValue> {
    for (i, &byte) in data.iter().enumerate() {
        let result = callback.call1(&JsValue::NULL, &JsValue::from_f64(i as f64))?;
        // 处理回调结果
    }
    Ok(())
}
```

**理论映射**: 回调机制 $\text{callback}: \text{WasmFunction} \leftrightarrow \text{JavaScriptFunction}$。

## 性能问题

### Q13: WebAssembly性能如何?

**A**: WebAssembly提供接近原生的性能：

```rust
// 高性能数值计算
#[wasm_bindgen]
pub fn matrix_multiply(a: &[f64], b: &[f64], size: usize) -> Vec<f64> {
    let mut result = vec![0.0; size * size];
    
    for i in 0..size {
        for j in 0..size {
            for k in 0..size {
                result[i * size + j] += a[i * size + k] * b[k * size + j];
            }
        }
    }
    
    result
}
```

**理论映射**: 性能模型 $\text{performance}(P_{\text{Wasm}}) \approx \text{performance}(P_{\text{Native}})$。

### Q14: 如何优化内存使用?

**A**: 使用内存优化策略：

```rust
// 使用内存池
#[wasm_bindgen]
pub struct MemoryPool {
    pool: Vec<Vec<u8>>,
}

impl MemoryPool {
    pub fn new() -> Self {
        Self { pool: Vec::new() }
    }
    
    pub fn allocate(&mut self, size: usize) -> &mut [u8] {
        if let Some(buffer) = self.pool.pop() {
            if buffer.len() >= size {
                return &mut buffer[..size];
            }
        }
        let mut new_buffer = vec![0; size];
        let result = &mut new_buffer[..size];
        self.pool.push(new_buffer);
        result
    }
}
```

**理论映射**: 内存优化 $\text{memory\_optimize}: \text{MemoryLayout} \rightarrow \text{OptimizedLayout}$。

### Q15: 如何实现并行计算?

**A**: 使用Web Workers或SIMD指令：

```rust
// 使用SIMD进行并行计算
#[target_feature(enable = "simd128")]
pub unsafe fn parallel_sum(data: &[f32]) -> f32 {
    let mut sum = 0.0f32;
    let chunk_size = 4; // SIMD向量大小
    
    for chunk in data.chunks(chunk_size) {
        // SIMD并行计算
        let simd_chunk = std::simd::Simd::from_slice(chunk);
        sum += simd_chunk.reduce_sum();
    }
    
    sum
}
```

**理论映射**: 并行执行 $\text{parallel}: \text{Tasks} \rightarrow \text{ConcurrentExecution}$。

### Q16: 如何监控性能指标?

**A**: 使用性能监控工具：

```rust
#[wasm_bindgen]
pub struct PerformanceMonitor {
    start_time: f64,
    measurements: Vec<f64>,
}

impl PerformanceMonitor {
    pub fn new() -> Self {
        Self {
            start_time: 0.0,
            measurements: Vec::new(),
        }
    }
    
    pub fn start_measurement(&mut self) {
        self.start_time = web_sys::window()
            .unwrap()
            .performance()
            .unwrap()
            .now();
    }
    
    pub fn end_measurement(&mut self) -> f64 {
        let end_time = web_sys::window()
            .unwrap()
            .performance()
            .unwrap()
            .now();
        let duration = end_time - self.start_time;
        self.measurements.push(duration);
        duration
    }
}
```

**理论映射**: 性能监控 $\text{monitor}: \text{Performance} \rightarrow \text{Metrics}$。

## 调试问题

### Q17: 如何调试WebAssembly代码?

**A**: 使用多种调试工具：

```rust
// 添加调试信息
#[wasm_bindgen]
pub fn debug_function(input: i32) -> i32 {
    // 使用console.log进行调试
    web_sys::console::log_1(&format!("Input: {}", input).into());
    
    let result = input * 2;
    
    web_sys::console::log_1(&format!("Output: {}", result).into());
    result
}
```

**理论映射**: 调试支持 $\text{debug}: \text{WasmModule} \rightarrow \text{DebugInfo}$。

### Q18: 如何处理运行时错误?

**A**: 实现错误处理机制：

```rust
#[wasm_bindgen]
pub fn safe_operation(input: &str) -> Result<String, String> {
    if input.is_empty() {
        return Err("Input cannot be empty".to_string());
    }
    
    if input.len() > 1000 {
        return Err("Input too long".to_string());
    }
    
    Ok(input.to_uppercase())
}
```

**理论映射**: 错误处理 $\text{error\_handle}: \text{Error} \rightarrow \text{Result}$。

### Q19: 如何分析内存泄漏?

**A**: 使用内存分析工具：

```rust
#[wasm_bindgen]
pub struct MemoryAnalyzer {
    allocations: HashMap<usize, usize>,
}

impl MemoryAnalyzer {
    pub fn new() -> Self {
        Self {
            allocations: HashMap::new(),
        }
    }
    
    pub fn track_allocation(&mut self, ptr: usize, size: usize) {
        self.allocations.insert(ptr, size);
    }
    
    pub fn track_deallocation(&mut self, ptr: usize) {
        self.allocations.remove(&ptr);
    }
    
    pub fn get_memory_usage(&self) -> usize {
        self.allocations.values().sum()
    }
}
```

**理论映射**: 内存分析 $\text{memory\_analyze}: \text{Memory} \rightarrow \text{MemoryReport}$。

### Q20: 如何验证代码正确性?

**A**: 使用形式化验证和测试：

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_safe_operation() {
        assert_eq!(safe_operation("hello").unwrap(), "HELLO");
        assert!(safe_operation("").is_err());
    }
    
    #[test]
    fn test_memory_safety() {
        let mut analyzer = MemoryAnalyzer::new();
        let ptr = 0x1000;
        analyzer.track_allocation(ptr, 1024);
        assert_eq!(analyzer.get_memory_usage(), 1024);
        analyzer.track_deallocation(ptr);
        assert_eq!(analyzer.get_memory_usage(), 0);
    }
}
```

**理论映射**: 代码验证 $\text{verify}: \text{Code} \rightarrow \text{Correctness}$。

## 部署问题

### Q21: 如何部署WebAssembly应用?

**A**: 使用多种部署策略：

```bash
# 构建生产版本
wasm-pack build --release --target web

# 部署到Web服务器
cp pkg/* /var/www/html/

# 部署到CDN
aws s3 cp pkg/ s3://my-bucket/ --recursive

# 部署到云函数
wasm-pack build --target nodejs
```

**理论映射**: 部署函数 $\text{deploy}: \text{WasmModule} \rightarrow \text{Deployment}$。

### Q22: 如何实现版本管理?

**A**: 使用版本控制策略：

```rust
#[wasm_bindgen]
pub struct VersionManager {
    version: String,
    compatibility: Vec<String>,
}

impl VersionManager {
    pub fn new(version: &str) -> Self {
        Self {
            version: version.to_string(),
            compatibility: vec!["1.0.0".to_string(), "1.1.0".to_string()],
        }
    }
    
    pub fn is_compatible(&self, other_version: &str) -> bool {
        self.compatibility.contains(&other_version.to_string())
    }
}
```

**理论映射**: 版本管理 $\text{version\_manage}: \text{Version} \rightarrow \text{Compatibility}$。

### Q23: 如何实现热更新?

**A**: 使用模块热更新机制：

```javascript
// 热更新实现
async function hotUpdate(newModuleUrl) {
    const newModule = await WebAssembly.instantiateStreaming(
        fetch(newModuleUrl),
        importObject
    );
    
    // 替换旧模块
    currentModule = newModule;
    
    // 通知应用更新
    notifyModuleUpdate();
}
```

**理论映射**: 热更新 $\text{hot\_update}: \text{OldModule} \rightarrow \text{NewModule}$。

### Q24: 如何监控部署状态?

**A**: 实现部署监控：

```rust
#[wasm_bindgen]
pub struct DeploymentMonitor {
    status: String,
    metrics: HashMap<String, f64>,
}

impl DeploymentMonitor {
    pub fn new() -> Self {
        Self {
            status: "deployed".to_string(),
            metrics: HashMap::new(),
        }
    }
    
    pub fn update_status(&mut self, status: &str) {
        self.status = status.to_string();
    }
    
    pub fn record_metric(&mut self, name: &str, value: f64) {
        self.metrics.insert(name.to_string(), value);
    }
}
```

**理论映射**: 部署监控 $\text{deploy\_monitor}: \text{Deployment} \rightarrow \text{Status}$。

## 安全问题

### Q25: WebAssembly是否安全?

**A**: WebAssembly提供多层安全机制：

```rust
// 沙箱执行示例
#[wasm_bindgen]
pub fn sandboxed_operation(input: &str) -> Result<String, String> {
    // 输入验证
    if input.len() > 1000 {
        return Err("Input too large".to_string());
    }
    
    // 资源限制
    if input.contains("dangerous") {
        return Err("Dangerous input detected".to_string());
    }
    
    // 安全处理
    Ok(input.to_uppercase())
}
```

**理论映射**: 安全保证 $\text{safe}(P_{\text{Wasm}}) \Rightarrow \text{sandboxed}(P_{\text{Wasm}})$。

### Q26: 如何防止内存攻击?

**A**: 使用内存安全机制：

```rust
#[wasm_bindgen]
pub fn safe_memory_access(ptr: usize, size: usize, memory_size: usize) -> Result<(), String> {
    // 边界检查
    if ptr + size > memory_size {
        return Err("Memory access out of bounds".to_string());
    }
    
    // 对齐检查
    if ptr % 4 != 0 {
        return Err("Unaligned memory access".to_string());
    }
    
    Ok(())
}
```

**理论映射**: 内存安全 $\forall \text{addr}, \text{size}: \text{addr} + \text{size} \leq |\text{Memory}|$。

### Q27: 如何实现访问控制?

**A**: 使用权限控制机制：

```rust
#[wasm_bindgen]
pub struct AccessControl {
    permissions: HashMap<String, Vec<String>>,
}

impl AccessControl {
    pub fn new() -> Self {
        let mut permissions = HashMap::new();
        permissions.insert("user".to_string(), vec!["read".to_string()]);
        permissions.insert("admin".to_string(), vec!["read".to_string(), "write".to_string()]);
        
        Self { permissions }
    }
    
    pub fn check_permission(&self, user: &str, action: &str) -> bool {
        if let Some(user_permissions) = self.permissions.get(user) {
            user_permissions.contains(&action.to_string())
        } else {
            false
        }
    }
}
```

**理论映射**: 访问控制 $\text{access\_control}: \text{User} \times \text{Action} \rightarrow \text{Permission}$。

### Q28: 如何审计安全事件?

**A**: 实现安全审计机制：

```rust
#[wasm_bindgen]
pub struct SecurityAuditor {
    events: Vec<SecurityEvent>,
}

#[derive(Serialize, Deserialize)]
pub struct SecurityEvent {
    timestamp: f64,
    event_type: String,
    details: String,
    severity: String,
}

impl SecurityAuditor {
    pub fn new() -> Self {
        Self { events: Vec::new() }
    }
    
    pub fn log_event(&mut self, event_type: &str, details: &str, severity: &str) {
        let event = SecurityEvent {
            timestamp: web_sys::window()
                .unwrap()
                .performance()
                .unwrap()
                .now(),
            event_type: event_type.to_string(),
            details: details.to_string(),
            severity: severity.to_string(),
        };
        self.events.push(event);
    }
}
```

**理论映射**: 安全审计 $\text{security\_audit}: \text{Event} \rightarrow \text{AuditLog}$。

## 兼容性问题

### Q29: 如何确保跨浏览器兼容性?

**A**: 使用兼容性检查和polyfill：

```rust
#[wasm_bindgen]
pub fn check_wasm_support() -> bool {
    // 检查WebAssembly支持
    web_sys::window()
        .unwrap()
        .WebAssembly()
        .is_some()
}

#[wasm_bindgen]
pub fn get_wasm_features() -> JsValue {
    let features = js_sys::Object::new();
    
    // 检查SIMD支持
    if web_sys::WebAssembly::simd_supported() {
        js_sys::Reflect::set(&features, &"simd".into(), &true.into()).unwrap();
    }
    
    // 检查线程支持
    if web_sys::WebAssembly::threads_supported() {
        js_sys::Reflect::set(&features, &"threads".into(), &true.into()).unwrap();
    }
    
    features.into()
}
```

**理论映射**: 兼容性检查 $\text{compatibility\_check}: \text{Environment} \rightarrow \text{Support}$。

### Q30: 如何处理版本兼容性?

**A**: 实现版本兼容性管理：

```rust
#[wasm_bindgen]
pub struct CompatibilityManager {
    current_version: String,
    supported_versions: Vec<String>,
}

impl CompatibilityManager {
    pub fn new(version: &str) -> Self {
        Self {
            current_version: version.to_string(),
            supported_versions: vec![
                "1.0.0".to_string(),
                "1.1.0".to_string(),
                "1.2.0".to_string(),
            ],
        }
    }
    
    pub fn is_compatible(&self, version: &str) -> bool {
        self.supported_versions.contains(&version.to_string())
    }
    
    pub fn migrate_data(&self, old_version: &str, data: &str) -> Result<String, String> {
        // 数据迁移逻辑
        match old_version {
            "1.0.0" => Ok(data.to_string()),
            "1.1.0" => Ok(data.to_string()),
            _ => Err("Unsupported version".to_string()),
        }
    }
}
```

**理论映射**: 版本兼容性 $\text{version\_compatibility}: \text{Version} \times \text{Version} \rightarrow \text{Compatible}$。

## 进阶问题

### Q21: WebAssembly的安全隔离机制是什么？

A: WebAssembly提供多层安全隔离：

1. **沙箱执行环境**：

    ```rust
    use wasmtime::{Engine, Module, Store, Instance};

    pub struct WasmSandbox {
        engine: Engine,
        store: Store<()>,
    }

    impl WasmSandbox {
        pub fn new() -> Self {
            let engine = Engine::default();
            let store = Store::new(&engine, ());
            
            Self { engine, store }
        }
        
        pub fn execute_isolated(&mut self, wasm_bytes: &[u8]) -> Result<(), WasmError> {
            // 创建隔离的模块实例
            let module = Module::new(&self.engine, wasm_bytes)?;
            let instance = Instance::new(&mut self.store, &module, &[])?;
            
            // 在沙箱中执行，无法访问主机系统
            // 只能通过预定义的接口与主机交互
            Ok(())
        }
    }
    ```

2. **内存隔离**：

```rust
use wasmtime::{Memory, MemoryType};

pub struct IsolatedMemory {
    memory: Memory,
    size_limit: u32,
}

impl IsolatedMemory {
    pub fn new(size_limit: u32) -> Self {
        let memory_type = MemoryType::new(1, Some(size_limit));
        let memory = Memory::new(&mut store, memory_type).unwrap();
        
        Self { memory, size_limit }
    }
    
    pub fn read_safe(&self, offset: u32, len: u32) -> Result<Vec<u8>, MemoryError> {
        if offset + len > self.size_limit {
            return Err(MemoryError::OutOfBounds);
        }
        
        let data = self.memory.read(&self.store, offset as usize, len as usize)?;
        Ok(data.to_vec())
    }
}
```

### Q22: 如何优化WebAssembly的性能？

A: WebAssembly性能优化策略：

1. **编译优化**：

    ```rust
    // Cargo.toml 配置
    [profile.release]
    opt-level = "z"  # 优化大小
    lto = true       # 链接时优化
    codegen-units = 1
    panic = "abort"

    # 使用 wasm-opt 进一步优化
    # wasm-opt -Oz -s 1000 target/wasm32-unknown-unknown/release/your_module.wasm
    ```

2. **内存管理优化**：

    ```rust
    use std::alloc::{GlobalAlloc, Layout, System};

    pub struct WasmAllocator;

    unsafe impl GlobalAlloc for WasmAllocator {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            // 使用WebAssembly的线性内存
            System.alloc(layout)
        }
        
        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            System.dealloc(ptr, layout);
        }
    }

    #[global_allocator]
    static ALLOCATOR: WasmAllocator = WasmAllocator;
    ```

3. **SIMD优化**：

```rust
use std::arch::wasm32::*;

pub fn simd_vector_add(a: &[f32], b: &[f32]) -> Vec<f32> {
    let mut result = Vec::with_capacity(a.len());
    
    for chunk in a.chunks_exact(4).zip(b.chunks_exact(4)) {
        let (a_chunk, b_chunk) = chunk;
        
        // 使用SIMD指令
        let a_simd = f32x4_load(a_chunk.as_ptr() as *const f32);
        let b_simd = f32x4_load(b_chunk.as_ptr() as *const f32);
        let sum = f32x4_add(a_simd, b_simd);
        
        // 存储结果
        let mut output = [0.0; 4];
        f32x4_store(output.as_mut_ptr() as *mut f32, sum);
        result.extend_from_slice(&output);
    }
    
    result
}
```

### Q23: Rust到WebAssembly的类型映射规则是什么？

A: 类型映射规则与最佳实践：

```rust
use wasm_bindgen::prelude::*;

// 基本类型映射
#[wasm_bindgen]
pub struct Point {
    x: f64,
    y: f64,
}

#[wasm_bindgen]
impl Point {
    #[wasm_bindgen(constructor)]
    pub fn new(x: f64, y: f64) -> Point {
        Point { x, y }
    }
    
    #[wasm_bindgen(getter)]
    pub fn x(&self) -> f64 {
        self.x
    }
    
    #[wasm_bindgen(setter)]
    pub fn set_x(&mut self, x: f64) {
        self.x = x;
    }
    
    // 复杂类型需要序列化
    pub fn to_json(&self) -> String {
        serde_json::to_string(self).unwrap()
    }
}

// 错误处理映射
#[wasm_bindgen]
pub enum WasmError {
    InvalidInput,
    ComputationError,
    MemoryError,
}

impl From<serde_json::Error> for WasmError {
    fn from(_: serde_json::Error) -> Self {
        WasmError::InvalidInput
    }
}

// 异步函数映射
#[wasm_bindgen]
pub async fn async_computation(input: &str) -> Result<String, WasmError> {
    // 异步计算逻辑
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    Ok(format!("Processed: {}", input))
}
```

### Q24: 如何在WebAssembly中实现多线程？

A: WebAssembly多线程实现：

```rust
use wasm_bindgen::prelude::*;
use web_sys::{Worker, MessageEvent, DedicatedWorkerGlobalScope};

#[wasm_bindgen]
pub struct WasmWorker {
    worker: Worker,
}

#[wasm_bindgen]
impl WasmWorker {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<WasmWorker, JsValue> {
        let worker = Worker::new("./worker.js")?;
        Ok(WasmWorker { worker })
    }
    
    pub fn post_message(&self, data: &str) -> Result<(), JsValue> {
        self.worker.post_message(&JsValue::from_str(data))?;
        Ok(())
    }
    
    pub fn set_onmessage(&self, callback: &js_sys::Function) {
        self.worker.set_onmessage(Some(callback));
    }
}

// 共享内存实现
use std::sync::atomic::{AtomicU32, Ordering};

#[wasm_bindgen]
pub struct SharedCounter {
    counter: AtomicU32,
}

#[wasm_bindgen]
impl SharedCounter {
    #[wasm_bindgen(constructor)]
    pub fn new() -> SharedCounter {
        SharedCounter {
            counter: AtomicU32::new(0),
        }
    }
    
    pub fn increment(&self) -> u32 {
        self.counter.fetch_add(1, Ordering::SeqCst)
    }
    
    pub fn get(&self) -> u32 {
        self.counter.load(Ordering::SeqCst)
    }
}
```

### Q25: WebAssembly与JavaScript的互操作性如何实现？

A: 互操作性实现策略：

```rust
use wasm_bindgen::prelude::*;
use js_sys::{Object, Reflect, Array};

// 1. 直接调用JavaScript函数
#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
    
    #[wasm_bindgen(js_namespace = Math)]
    fn random() -> f64;
}

// 2. 传递复杂对象
#[wasm_bindgen]
pub fn process_js_object(obj: &Object) -> Result<String, JsValue> {
    let name = Reflect::get(obj, &JsValue::from_str("name"))?
        .as_string()
        .unwrap_or_default();
    
    let age = Reflect::get(obj, &JsValue::from_str("age"))?
        .as_f64()
        .unwrap_or(0.0) as u32;
    
    Ok(format!("Name: {}, Age: {}", name, age))
}

// 3. 返回JavaScript对象
#[wasm_bindgen]
pub fn create_js_object(name: &str, age: u32) -> Object {
    let obj = Object::new();
    Reflect::set(&obj, &JsValue::from_str("name"), &JsValue::from_str(name)).unwrap();
    Reflect::set(&obj, &JsValue::from_str("age"), &JsValue::from_f64(age as f64)).unwrap();
    obj
}

// 4. 处理JavaScript数组
#[wasm_bindgen]
pub fn process_js_array(arr: &Array) -> Array {
    let result = Array::new();
    
    for i in 0..arr.length() {
        if let Some(value) = arr.get(i).as_f64() {
            result.push(&JsValue::from_f64(value * 2.0));
        }
    }
    
    result
}

// 5. 异步JavaScript调用
#[wasm_bindgen]
pub async fn fetch_data(url: &str) -> Result<String, JsValue> {
    let promise = js_sys::Reflect::get(
        &js_sys::global(),
        &JsValue::from_str("fetch")
    )?;
    
    let response = js_sys::Reflect::apply(
        &promise,
        &js_sys::global(),
        &Array::of1(&JsValue::from_str(url))
    )?;
    
    // 处理响应...
    Ok("Data fetched".to_string())
}
```

### Q26: WebAssembly的内存管理最佳实践是什么？

A: 内存管理策略：

```rust
use std::alloc::{GlobalAlloc, Layout, System};
use std::ptr::NonNull;

// 1. 自定义分配器
pub struct WasmAllocator {
    base_ptr: *mut u8,
    current_offset: usize,
    total_size: usize,
}

unsafe impl GlobalAlloc for WasmAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let align = layout.align();
        let size = layout.size();
        
        // 对齐到下一个边界
        let aligned_offset = (self.current_offset + align - 1) & !(align - 1);
        
        if aligned_offset + size > self.total_size {
            return std::ptr::null_mut();
        }
        
        self.base_ptr.add(aligned_offset)
    }
    
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        // WebAssembly中通常不需要显式释放
        // 内存会在模块卸载时自动回收
    }
}

// 2. 内存池管理
pub struct MemoryPool {
    blocks: Vec<MemoryBlock>,
    free_blocks: Vec<usize>,
}

struct MemoryBlock {
    ptr: *mut u8,
    size: usize,
    in_use: bool,
}

impl MemoryPool {
    pub fn new(total_size: usize, block_size: usize) -> Self {
        let num_blocks = total_size / block_size;
        let mut blocks = Vec::with_capacity(num_blocks);
        let mut free_blocks = Vec::with_capacity(num_blocks);
        
        for i in 0..num_blocks {
            let ptr = unsafe { System.alloc(Layout::from_size_align(block_size, 8).unwrap()) };
            blocks.push(MemoryBlock {
                ptr,
                size: block_size,
                in_use: false,
            });
            free_blocks.push(i);
        }
        
        Self { blocks, free_blocks }
    }
    
    pub fn allocate(&mut self, size: usize) -> Option<*mut u8> {
        for &block_idx in &self.free_blocks {
            if self.blocks[block_idx].size >= size {
                self.blocks[block_idx].in_use = true;
                self.free_blocks.retain(|&x| x != block_idx);
                return Some(self.blocks[block_idx].ptr);
            }
        }
        None
    }
    
    pub fn deallocate(&mut self, ptr: *mut u8) {
        for (i, block) in self.blocks.iter_mut().enumerate() {
            if block.ptr == ptr && block.in_use {
                block.in_use = false;
                self.free_blocks.push(i);
                break;
            }
        }
    }
}

// 3. 零拷贝数据传输
#[wasm_bindgen]
pub struct ZeroCopyBuffer {
    data: Vec<u8>,
    offset: usize,
}

#[wasm_bindgen]
impl ZeroCopyBuffer {
    #[wasm_bindgen(constructor)]
    pub fn new(size: usize) -> ZeroCopyBuffer {
        ZeroCopyBuffer {
            data: vec![0; size],
            offset: 0,
        }
    }
    
    pub fn write(&mut self, input: &[u8]) -> Result<usize, JsValue> {
        let remaining = self.data.len() - self.offset;
        let write_size = std::cmp::min(input.len(), remaining);
        
        self.data[self.offset..self.offset + write_size].copy_from_slice(&input[..write_size]);
        self.offset += write_size;
        
        Ok(write_size)
    }
    
    pub fn read(&self, start: usize, len: usize) -> Result<Vec<u8>, JsValue> {
        if start + len > self.data.len() {
            return Err(JsValue::from_str("Out of bounds"));
        }
        
        Ok(self.data[start..start + len].to_vec())
    }
}
```

## 交叉引用与扩展阅读

### 相关文档

- WebAssembly理论：`01_webassembly_theory.md`
- WebAssembly实现：`02_webassembly_implementation.md`
- 编译理论：`03_compilation_theory.md`
- Rust到WASM：`04_rust_to_wasm.md`

### 外部资源

- [wasm-bindgen](https://github.com/rustwasm/wasm-bindgen) - Rust与JavaScript绑定
- [wasm-pack](https://github.com/rustwasm/wasm-pack) - WebAssembly打包工具
- [wasmtime](https://github.com/bytecodealliance/wasmtime) - WebAssembly运行时
- [WebAssembly规范](https://webassembly.github.io/spec/) - 官方规范文档

### 快速导航

- 模型理论（Rust语义映射）：`../18_model/01_model_theory.md`
- IoT常见问题：`../17_iot/FAQ.md`
- 分布式系统FAQ：`../../crates/c20_distributed/docs/FAQ.md`
- AI系统FAQ：`../../crates/c19_ai/docs/FAQ.md`

### 练习与思考

1. 将一个包含 `Vec<f32>` 数据处理的 Rust 函数迁移到 WASM，比较 `-O3` 与 `-Oz` 下的体积与性能变化，解释优化权衡。
2. 设计一个 `wasm-bindgen` 互操作接口，要求在 JS 中传入复杂对象并在 Rust 内进行校验与序列化；给出边界条件测试。
3. 在 `wasmtime` 运行时中开启 `SIMD` 与 `wasi`，编写基准程序评估内存、CPU 使用与延迟并给出结果分析。

### 性能优化工具

- [wasm-opt](https://github.com/WebAssembly/binaryen) - WebAssembly优化器
- [twiggy](https://github.com/rustwasm/twiggy) - WebAssembly分析工具
- [wasm-bindgen-test](https://github.com/rustwasm/wasm-bindgen) - WebAssembly测试框架

---

**文档状态**: 完成  
**最后更新**: 2025-01-27  
**维护者**: Rust形式化理论项目组
