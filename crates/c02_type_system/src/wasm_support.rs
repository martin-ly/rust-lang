//! WebAssembly 支持模块
//!
//! 本模块展示了 Rust 1.90 中的 WebAssembly 支持特性，包括：
//! - WASM 基础类型和操作
//! - 内存管理
//! - 函数导出和导入
//! - 性能优化
//! - 与 JavaScript 的互操作
//!
//! # 文件信息
//! - 文件: wasm_support.rs
//! - 创建日期: 2025-01-27
//! - 版本: 1.0
//! - Rust版本: 1.90.0
//! - Edition: 2024

use std::collections::HashMap;
use std::sync::Mutex;

// ==================== 1. WASM 基础类型和操作 ====================

/// WASM 基础数据类型
/// 
/// 展示了 WebAssembly 中的基础数据类型
#[derive(Debug, Clone, PartialEq)]
pub enum WasmType {
    /// 32位整数
    I32(i32),
    /// 64位整数
    I64(i64),
    /// 32位浮点数
    F32(f32),
    /// 64位浮点数
    F64(f64),
}

impl WasmType {
    /// 转换为 i32
    pub fn to_i32(&self) -> i32 {
        match self {
            WasmType::I32(val) => *val,
            WasmType::I64(val) => *val as i32,
            WasmType::F32(val) => *val as i32,
            WasmType::F64(val) => *val as i32,
        }
    }
    
    /// 转换为 f64
    pub fn to_f64(&self) -> f64 {
        match self {
            WasmType::I32(val) => *val as f64,
            WasmType::I64(val) => *val as f64,
            WasmType::F32(val) => *val as f64,
            WasmType::F64(val) => *val,
        }
    }
    
    /// 类型转换
    pub fn convert_to(&self, target_type: WasmTypeKind) -> WasmType {
        match target_type {
            WasmTypeKind::I32 => WasmType::I32(self.to_i32()),
            WasmTypeKind::I64 => WasmType::I64(self.to_i32() as i64),
            WasmTypeKind::F32 => WasmType::F32(self.to_f64() as f32),
            WasmTypeKind::F64 => WasmType::F64(self.to_f64()),
        }
    }
}

/// WASM 类型种类
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum WasmTypeKind {
    I32,
    I64,
    F32,
    F64,
}

/// WASM 基础操作
pub struct WasmOperations;

impl WasmOperations {
    /// 加法操作
    pub fn add(a: WasmType, b: WasmType) -> WasmType {
        match (a, b) {
            (WasmType::I32(x), WasmType::I32(y)) => WasmType::I32(x + y),
            (WasmType::I64(x), WasmType::I64(y)) => WasmType::I64(x + y),
            (WasmType::F32(x), WasmType::F32(y)) => WasmType::F32(x + y),
            (WasmType::F64(x), WasmType::F64(y)) => WasmType::F64(x + y),
            (a, b) => {
                // 类型不匹配时进行转换
                let a_f64 = a.to_f64();
                let b_f64 = b.to_f64();
                WasmType::F64(a_f64 + b_f64)
            }
        }
    }
    
    /// 乘法操作
    pub fn multiply(a: WasmType, b: WasmType) -> WasmType {
        match (a, b) {
            (WasmType::I32(x), WasmType::I32(y)) => WasmType::I32(x * y),
            (WasmType::I64(x), WasmType::I64(y)) => WasmType::I64(x * y),
            (WasmType::F32(x), WasmType::F32(y)) => WasmType::F32(x * y),
            (WasmType::F64(x), WasmType::F64(y)) => WasmType::F64(x * y),
            (a, b) => {
                let a_f64 = a.to_f64();
                let b_f64 = b.to_f64();
                WasmType::F64(a_f64 * b_f64)
            }
        }
    }
    
    /// 比较操作
    pub fn compare(a: WasmType, b: WasmType) -> i32 {
        match (a, b) {
            (WasmType::I32(x), WasmType::I32(y)) => {
                if x == y { 0 } else if x < y { -1 } else { 1 }
            },
            (WasmType::I64(x), WasmType::I64(y)) => {
                if x == y { 0 } else if x < y { -1 } else { 1 }
            },
            (WasmType::F32(x), WasmType::F32(y)) => {
                if x == y { 0 } else if x < y { -1 } else { 1 }
            },
            (WasmType::F64(x), WasmType::F64(y)) => {
                if x == y { 0 } else if x < y { -1 } else { 1 }
            },
            (a, b) => {
                let a_f64 = a.to_f64();
                let b_f64 = b.to_f64();
                if (a_f64 - b_f64).abs() < f64::EPSILON { 0 } 
                else if a_f64 < b_f64 { -1 } 
                else { 1 }
            }
        }
    }
}

// ==================== 2. WASM 内存管理 ====================

/// WASM 内存管理器
/// 
/// 展示了 WebAssembly 中的内存管理特性
pub struct WasmMemoryManager {
    /// 线性内存
    memory: Vec<u8>,
    /// 内存大小（以页为单位，每页64KB）
    pages: u32,
    /// 最大内存页数
    max_pages: u32,
    /// 内存使用统计
    usage_stats: Mutex<MemoryUsageStats>,
}

/// 内存使用统计
#[derive(Debug, Default)]
pub struct MemoryUsageStats {
    pub allocated_bytes: usize,
    pub free_bytes: usize,
    pub total_allocations: u64,
    pub total_deallocations: u64,
}

impl WasmMemoryManager {
    /// 创建新的内存管理器
    pub fn new(initial_pages: u32, max_pages: u32) -> Self {
        let page_size = 64 * 1024; // 64KB per page
        let memory_size = initial_pages as usize * page_size;
        
        Self {
            memory: vec![0; memory_size],
            pages: initial_pages,
            max_pages,
            usage_stats: Mutex::new(MemoryUsageStats::default()),
        }
    }
    
    /// 分配内存
    pub fn allocate(&self, size: usize) -> Option<usize> {
        let mut stats = self.usage_stats.lock().unwrap();
        
        // 简单的线性分配策略
        if stats.allocated_bytes + size <= self.memory.len() {
            let offset = stats.allocated_bytes;
            stats.allocated_bytes += size;
            stats.total_allocations += 1;
            Some(offset)
        } else {
            None
        }
    }
    
    /// 释放内存
    pub fn deallocate(&self, _offset: usize, _size: usize) {
        let mut stats = self.usage_stats.lock().unwrap();
        stats.total_deallocations += 1;
        // 简化实现，实际WASM中内存管理更复杂
    }
    
    /// 写入数据
    pub fn write(&mut self, offset: usize, data: &[u8]) -> Result<(), String> {
        if offset + data.len() > self.memory.len() {
            return Err("Memory access out of bounds".to_string());
        }
        
        self.memory[offset..offset + data.len()].copy_from_slice(data);
        Ok(())
    }
    
    /// 读取数据
    pub fn read(&self, offset: usize, size: usize) -> Result<&[u8], String> {
        if offset + size > self.memory.len() {
            return Err("Memory access out of bounds".to_string());
        }
        
        Ok(&self.memory[offset..offset + size])
    }
    
    /// 获取内存使用统计
    pub fn get_usage_stats(&self) -> MemoryUsageStats {
        self.usage_stats.lock().unwrap().clone()
    }
    
    /// 获取当前内存页数
    pub fn get_pages(&self) -> u32 {
        self.pages
    }
    
    /// 扩展内存
    pub fn grow_memory(&mut self, additional_pages: u32) -> Result<u32, String> {
        if self.pages + additional_pages > self.max_pages {
            return Err("Cannot grow memory beyond maximum pages".to_string());
        }
        
        let page_size = 64 * 1024;
        let additional_bytes = additional_pages as usize * page_size;
        self.memory.resize(self.memory.len() + additional_bytes, 0);
        
        let old_pages = self.pages;
        self.pages += additional_pages;
        Ok(old_pages)
    }
}


impl Clone for MemoryUsageStats {
    fn clone(&self) -> Self {
        Self {
            allocated_bytes: self.allocated_bytes,
            free_bytes: self.free_bytes,
            total_allocations: self.total_allocations,
            total_deallocations: self.total_deallocations,
        }
    }
}

// ==================== 3. WASM 函数导出和导入 ====================

/// WASM 函数导出器
/// 
/// 展示了 WebAssembly 中的函数导出机制
pub struct WasmFunctionExporter {
    /// 导出的函数表
    functions: HashMap<String, WasmFunction>,
}

/// WASM 函数定义
pub struct WasmFunction {
    pub name: String,
    pub parameters: Vec<WasmTypeKind>,
    pub return_type: Option<WasmTypeKind>,
    pub implementation: Box<dyn Fn(Vec<WasmType>) -> Result<WasmType, String> + Send + Sync>,
}

impl WasmFunctionExporter {
    /// 创建新的函数导出器
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
        }
    }
    
    /// 导出函数
    pub fn export_function<F>(&mut self, name: String, func: F) -> Result<(), String>
    where
        F: Fn(Vec<WasmType>) -> Result<WasmType, String> + Send + Sync + 'static,
    {
        if self.functions.contains_key(&name) {
            return Err(format!("Function '{}' already exported", name));
        }
        
        let wasm_func = WasmFunction {
            name: name.clone(),
            parameters: vec![], // 简化实现
            return_type: Some(WasmTypeKind::I32),
            implementation: Box::new(func),
        };
        
        self.functions.insert(name, wasm_func);
        Ok(())
    }
    
    /// 调用导出的函数
    pub fn call_function(&self, name: &str, args: Vec<WasmType>) -> Result<WasmType, String> {
        let func = self.functions.get(name)
            .ok_or_else(|| format!("Function '{}' not found", name))?;
        
        (func.implementation)(args)
    }
    
    /// 获取所有导出的函数名
    pub fn get_exported_functions(&self) -> Vec<String> {
        self.functions.keys().cloned().collect()
    }
}

impl Default for WasmFunctionExporter {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 4. WASM 性能优化 ====================

/// WASM 性能优化器
/// 
/// 展示了 WebAssembly 中的性能优化技术
pub struct WasmPerformanceOptimizer {
    /// 优化统计
    stats: Mutex<OptimizationStats>,
}

/// 优化统计
#[derive(Debug, Default)]
pub struct OptimizationStats {
    pub function_calls: u64,
    pub memory_accesses: u64,
    pub type_conversions: u64,
    pub optimizations_applied: u64,
}

impl WasmPerformanceOptimizer {
    /// 创建新的性能优化器
    pub fn new() -> Self {
        Self {
            stats: Mutex::new(OptimizationStats::default()),
        }
    }
    
    /// 优化函数调用
    pub fn optimize_function_call<F, R>(&self, func: F, args: Vec<WasmType>) -> Result<R, String>
    where
        F: Fn(Vec<WasmType>) -> Result<R, String>,
    {
        let mut stats = self.stats.lock().unwrap();
        stats.function_calls += 1;
        
        // 应用优化
        let optimized_args = self.optimize_arguments(args);
        stats.optimizations_applied += 1;
        
        func(optimized_args)
    }
    
    /// 优化参数
    fn optimize_arguments(&self, args: Vec<WasmType>) -> Vec<WasmType> {
        let mut stats = self.stats.lock().unwrap();
        stats.type_conversions += 1;
        
        // 简化优化：确保类型一致性
        args.into_iter().map(|arg| {
            match arg {
                WasmType::F32(val) if val.fract() == 0.0 => WasmType::I32(val as i32),
                WasmType::F64(val) if val.fract() == 0.0 => WasmType::I64(val as i64),
                other => other,
            }
        }).collect()
    }
    
    /// 优化内存访问
    pub fn optimize_memory_access(&self, offset: usize, size: usize) -> (usize, usize) {
        let mut stats = self.stats.lock().unwrap();
        stats.memory_accesses += 1;
        
        // 内存对齐优化
        let aligned_offset = (offset + 7) & !7; // 8字节对齐
        let aligned_size = ((size + 7) & !7).max(8); // 最小8字节
        
        stats.optimizations_applied += 1;
        (aligned_offset, aligned_size)
    }
    
    /// 获取优化统计
    pub fn get_stats(&self) -> OptimizationStats {
        self.stats.lock().unwrap().clone()
    }
}

impl Default for WasmPerformanceOptimizer {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for OptimizationStats {
    fn clone(&self) -> Self {
        Self {
            function_calls: self.function_calls,
            memory_accesses: self.memory_accesses,
            type_conversions: self.type_conversions,
            optimizations_applied: self.optimizations_applied,
        }
    }
}

// ==================== 5. 与 JavaScript 的互操作 ====================

/// JavaScript 互操作接口
/// 
/// 展示了 Rust 与 JavaScript 的互操作特性
pub struct JsInterop {
    /// 回调函数注册表
    callbacks: Mutex<HashMap<String, Box<dyn Fn(String) -> String + Send + Sync>>>,
}

impl JsInterop {
    /// 创建新的 JavaScript 互操作接口
    pub fn new() -> Self {
        Self {
            callbacks: Mutex::new(HashMap::new()),
        }
    }
    
    /// 注册回调函数
    pub fn register_callback<F>(&self, name: String, callback: F) -> Result<(), String>
    where
        F: Fn(String) -> String + Send + Sync + 'static,
    {
        let mut callbacks = self.callbacks.lock().unwrap();
        if callbacks.contains_key(&name) {
            return Err(format!("Callback '{}' already registered", name));
        }
        
        callbacks.insert(name, Box::new(callback));
        Ok(())
    }
    
    /// 调用 JavaScript 函数（模拟）
    pub fn call_js_function(&self, name: &str, args: &str) -> String {
        // 在实际WASM环境中，这里会调用真实的JavaScript函数
        format!("JS_FUNCTION_CALL: {}({})", name, args)
    }
    
    /// 处理来自 JavaScript 的调用
    pub fn handle_js_call(&self, name: &str, data: String) -> String {
        let callbacks = self.callbacks.lock().unwrap();
        if let Some(callback) = callbacks.get(name) {
            callback(data)
        } else {
            format!("No callback registered for '{}'", name)
        }
    }
    
    /// 获取所有注册的回调
    pub fn get_registered_callbacks(&self) -> Vec<String> {
        let callbacks = self.callbacks.lock().unwrap();
        callbacks.keys().cloned().collect()
    }
}

impl Default for JsInterop {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 演示函数 ====================

/// 演示所有 WASM 特性
pub fn demonstrate_wasm_features() {
    println!("=== WebAssembly 特性演示 ===\n");
    
    // 1. 基础类型和操作演示
    println!("1. WASM 基础类型和操作演示:");
    let a = WasmType::I32(10);
    let b = WasmType::I32(20);
    let sum = WasmOperations::add(a, b);
    println!("  10 + 20 = {:?}", sum);
    
    let c = WasmType::F64(std::f64::consts::PI);
    let d = WasmType::F64(2.86);
    let product = WasmOperations::multiply(c, d);
    println!("  3.14 * 2.86 = {:?}", product);
    
    let comparison = WasmOperations::compare(WasmType::I32(5), WasmType::I32(3));
    println!("  5 vs 3 比较结果: {}", comparison);
    println!();
    
    // 2. 内存管理演示
    println!("2. WASM 内存管理演示:");
    let mut memory_manager = WasmMemoryManager::new(1, 10); // 1页初始，最大10页
    
    let offset = memory_manager.allocate(100).unwrap();
    println!("  分配100字节，偏移: {}", offset);
    
    let data = b"Hello, WASM!";
    let _ = memory_manager.write(offset, data);
    println!("  写入数据: {:?}", data);
    
    let read_data = memory_manager.read(offset, data.len()).unwrap();
    println!("  读取数据: {:?}", read_data);
    
    let stats = memory_manager.get_usage_stats();
    println!("  内存统计: {:?}", stats);
    
    let old_pages = memory_manager.grow_memory(1).unwrap();
    println!("  扩展内存，旧页数: {}, 新页数: {}", old_pages, memory_manager.get_pages());
    println!();
    
    // 3. 函数导出演示
    println!("3. WASM 函数导出演示:");
    let mut exporter = WasmFunctionExporter::new();
    
    let _ = exporter.export_function("add".to_string(), |args| {
        if args.len() != 2 {
            return Err("Expected 2 arguments".to_string());
        }
        Ok(WasmOperations::add(args[0].clone(), args[1].clone()))
    });
    
    let _ = exporter.export_function("multiply".to_string(), |args| {
        if args.len() != 2 {
            return Err("Expected 2 arguments".to_string());
        }
        Ok(WasmOperations::multiply(args[0].clone(), args[1].clone()))
    });
    
    let exported_functions = exporter.get_exported_functions();
    println!("  导出的函数: {:?}", exported_functions);
    
    let result = exporter.call_function("add", vec![WasmType::I32(15), WasmType::I32(25)]);
    println!("  调用 add(15, 25): {:?}", result);
    
    let result = exporter.call_function("multiply", vec![WasmType::F32(2.5), WasmType::F32(4.0)]);
    println!("  调用 multiply(2.5, 4.0): {:?}", result);
    println!();
    
    // 4. 性能优化演示
    println!("4. WASM 性能优化演示:");
    let optimizer = WasmPerformanceOptimizer::new();
    
    let result = optimizer.optimize_function_call(|args| {
        Ok(WasmOperations::add(args[0].clone(), args[1].clone()))
    }, vec![WasmType::F32(10.0), WasmType::F32(20.0)]);
    println!("  优化函数调用结果: {:?}", result);
    
    let (aligned_offset, aligned_size) = optimizer.optimize_memory_access(15, 7);
    println!("  内存访问优化: 偏移 {} -> {}, 大小 {} -> {}", 15, aligned_offset, 7, aligned_size);
    
    let stats = optimizer.get_stats();
    println!("  优化统计: {:?}", stats);
    println!();
    
    // 5. JavaScript 互操作演示
    println!("5. JavaScript 互操作演示:");
    let js_interop = JsInterop::new();
    
    let _ = js_interop.register_callback("process_data".to_string(), |data| {
        format!("Processed: {}", data.to_uppercase())
    });
    
    let _ = js_interop.register_callback("format_output".to_string(), |data| {
        format!("[FORMATTED] {}", data)
    });
    
    let callbacks = js_interop.get_registered_callbacks();
    println!("  注册的回调: {:?}", callbacks);
    
    let js_result = js_interop.call_js_function("console.log", "Hello from Rust!");
    println!("  调用 JS 函数: {}", js_result);
    
    let callback_result = js_interop.handle_js_call("process_data", "hello world".to_string());
    println!("  回调处理结果: {}", callback_result);
    
    println!("\n=== WebAssembly 特性演示完成 ===");
}

// ==================== 测试模块 ====================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_wasm_operations() {
        let a = WasmType::I32(10);
        let b = WasmType::I32(20);
        let sum = WasmOperations::add(a, b);
        assert_eq!(sum, WasmType::I32(30));
        
        let product = WasmOperations::multiply(WasmType::F32(2.0), WasmType::F32(3.0));
        assert_eq!(product, WasmType::F32(6.0));
    }
    
    #[test]
    fn test_memory_manager() {
        let mut manager = WasmMemoryManager::new(1, 10);
        let offset = manager.allocate(100).unwrap();
        assert_eq!(offset, 0);
        
        let data = b"test";
        let _ = manager.write(offset, data);
        let read_data = manager.read(offset, data.len()).unwrap();
        assert_eq!(read_data, data);
    }
    
    #[test]
    fn test_function_exporter() {
        let mut exporter = WasmFunctionExporter::new();
        let _ = exporter.export_function("test".to_string(), |_| Ok(WasmType::I32(42)));
        
        let result = exporter.call_function("test", vec![]);
        assert_eq!(result, Ok(WasmType::I32(42)));
    }
    
    #[test]
    fn test_js_interop() {
        let interop = JsInterop::new();
        let _ = interop.register_callback("test".to_string(), |data| format!("echo: {}", data));
        
        let result = interop.handle_js_call("test", "hello".to_string());
        assert_eq!(result, "echo: hello");
    }
}
