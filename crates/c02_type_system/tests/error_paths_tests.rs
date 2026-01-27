//! 类型系统模块错误路径测试套件 / Type System Module Error Paths Test Suite

use c02_type_system::wasm_support::{WasmFunctionExporter, WasmMemoryManager};

/// 测试错误输入情况
#[test]
fn test_error_inputs() {
    // WASM 函数导出器：重复导出同名函数应返回错误
    let mut exporter = WasmFunctionExporter::new();
    exporter
        .export_function("f".to_string(), |_args| Ok(c02_type_system::wasm_support::WasmType::I32(1)))
        .unwrap();

    assert!(exporter
        .export_function("f".to_string(), |_args| Ok(c02_type_system::wasm_support::WasmType::I32(2)))
        .is_err());
}

/// 测试错误状态情况
#[test]
fn test_error_states() {
    // 调用不存在的函数应返回错误
    let exporter = WasmFunctionExporter::new();
    assert!(exporter.call_function("missing", vec![]).is_err());
}

/// 测试异常情况
#[test]
fn test_exception_cases() {
    // WASM 内存越界读写应返回错误
    let mut mem = WasmMemoryManager::new(1, 1); // 64KB
    let too_large_offset = 64 * 1024 - 1;
    assert!(mem.write(too_large_offset, &[1, 2, 3]).is_err());
    assert!(mem.read(too_large_offset, 10).is_err());
}

/// 测试资源耗尽情况
#[test]
fn test_resource_exhaustion() {
    // 内存增长超过 max_pages 应返回错误
    let mut mem = WasmMemoryManager::new(1, 1);
    assert!(mem.grow_memory(1).is_err());
}

/// 测试并发安全
#[test]
fn test_concurrent_safety() {
    use std::sync::{Arc, Mutex};
    use std::thread;

    let shared = Arc::new(Mutex::new(Vec::<i32>::new()));
    let mut handles = vec![];

    // 创建多个线程同时操作
    for i in 0..10 {
        let shared = Arc::clone(&shared);
        let handle = thread::spawn(move || {
            let mut vec = shared.lock().unwrap();
            vec.push(i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 验证所有值都已添加
    let vec = shared.lock().unwrap();
    assert_eq!(vec.len(), 10);
}
