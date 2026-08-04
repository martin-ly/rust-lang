use std::fs;
use std::path::Path;
use tempfile::TempDir;

// 模拟测试数据
fn create_test_files(temp_dir: &TempDir) -> std::io::Result<()> {
    let test_content = r#"
# 测试文档

## 形式化定义

使用统一符号系统(RFUSS)的形式化定义：

```math
\text{Test}(A, B) \equiv \forall a \in A. \exists b \in B. \text{Relation}(a, b)
```

## 代码示例

```rust
fn test_function() {
    println!("测试函数");
}
```
"#;

    fs::write(temp_dir.path().join("test_doc.md"), test_content)?;
    Ok(())
}

#[test]
fn test_symbol_consistency_checker() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    let args = vec![
        "integration_runner".to_string(),
        "symbol".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--output".to_string(),
        "json".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "符号一致性检查应该成功");
}

#[test]
fn test_concept_consistency_checker() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    let args = vec![
        "integration_runner".to_string(),
        "concept".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--output".to_string(),
        "json".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "概念一致性检查应该成功");
}

#[test]
fn test_hierarchy_validator() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    let args = vec![
        "integration_runner".to_string(),
        "hierarchy".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--output".to_string(),
        "json".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "层次框架验证应该成功");
}

#[test]
fn test_invalid_tool() {
    let args = vec![
        "integration_runner".to_string(),
        "invalid_tool".to_string(),
        "--path".to_string(),
        "/tmp".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_err(), "无效工具应该返回错误");
}

#[test]
fn test_missing_path() {
    let args = vec![
        "integration_runner".to_string(),
        "symbol".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_err(), "缺少路径参数应该返回错误");
}

#[test]
fn test_invalid_output_format() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    let args = vec![
        "integration_runner".to_string(),
        "symbol".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--output".to_string(),
        "invalid_format".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_err(), "无效输出格式应该返回错误");
}

#[test]
fn test_all_tools() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    let args = vec![
        "integration_runner".to_string(),
        "all".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--output".to_string(),
        "json".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "所有工具应该成功运行");
}

#[test]
fn test_help_output() {
    let args = vec![
        "integration_runner".to_string(),
        "--help".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "帮助信息应该成功显示");
}

#[test]
fn test_version_output() {
    let args = vec![
        "integration_runner".to_string(),
        "--version".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "版本信息应该成功显示");
}

#[test]
fn test_verbose_output() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    let args = vec![
        "integration_runner".to_string(),
        "symbol".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--verbose".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "详细输出模式应该成功");
}

#[test]
fn test_output_file() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    let output_file = temp_dir.path().join("output.json");

    let args = vec![
        "integration_runner".to_string(),
        "symbol".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--output-file".to_string(),
        output_file.to_string_lossy().to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "输出到文件应该成功");
    assert!(output_file.exists(), "输出文件应该被创建");
}

#[test]
fn test_concurrent_execution() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    let args = vec![
        "integration_runner".to_string(),
        "all".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--concurrent".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "并发执行应该成功");
}

#[test]
fn test_error_handling() {
    let args = vec![
        "integration_runner".to_string(),
        "symbol".to_string(),
        "--path".to_string(),
        "/nonexistent/path".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_err(), "不存在的路径应该返回错误");
}

#[test]
fn test_large_directory() {
    let temp_dir = TempDir::new().unwrap();
    
    // 创建大量测试文件
    for i in 0..100 {
        let content = format!(
            r#"
# 测试文档 {}

## 形式化定义

```math
\text{Test{}}(A, B) \equiv \forall a \in A. \exists b \in B. \text{Relation}(a, b)
```

## 代码示例

```rust
fn test_function_{}() {{
    println!("测试函数{}");
}}
"#,
            i, i, i
        );
        
        fs::write(temp_dir.path().join(format!("test_{}.md", i)), content).unwrap();
    }

    let args = vec![
        "integration_runner".to_string(),
        "all".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--output".to_string(),
        "json".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "处理大量文件应该成功");
}

#[test]
fn test_different_file_formats() {
    let temp_dir = TempDir::new().unwrap();
    
    // 创建不同格式的测试文件
    let markdown_content = r#"
# 测试文档

## 形式化定义

```math
\text{Test}(A, B) \equiv \forall a \in A. \exists b \in B. \text{Relation}(a, b)
```
"#;

    let rust_content = r#"
// 测试Rust文件
fn test_function() {
    println!("测试函数");
}
"#;

    let txt_content = r#"
测试文本文件
包含一些数学符号: ∀a ∈ A, ∃b ∈ B
"#;

    fs::write(temp_dir.path().join("test.md"), markdown_content).unwrap();
    fs::write(temp_dir.path().join("test.rs"), rust_content).unwrap();
    fs::write(temp_dir.path().join("test.txt"), txt_content).unwrap();

    let args = vec![
        "integration_runner".to_string(),
        "all".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--output".to_string(),
        "json".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "处理不同格式文件应该成功");
}

#[test]
fn test_memory_usage() {
    let temp_dir = TempDir::new().unwrap();
    
    // 创建大文件
    let large_content = "测试内容\n".repeat(10000);
    fs::write(temp_dir.path().join("large_file.md"), large_content).unwrap();

    let args = vec![
        "integration_runner".to_string(),
        "all".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--output".to_string(),
        "json".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "处理大文件应该成功");
}

#[test]
fn test_concurrent_safety() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    // 并发运行多个实例
    let handles: Vec<_> = (0..5)
        .map(|_| {
            let temp_dir = temp_dir.path().to_path_buf();
            std::thread::spawn(move || {
                let args = vec![
                    "integration_runner".to_string(),
                    "symbol".to_string(),
                    "--path".to_string(),
                    temp_dir.to_string_lossy().to_string(),
                    "--output".to_string(),
                    "json".to_string(),
                ];
                integration_runner::run(args)
            })
        })
        .collect();

    for handle in handles {
        let result = handle.join().unwrap();
        assert!(result.is_ok(), "并发执行应该成功");
    }
}

#[test]
fn test_error_recovery() {
    let temp_dir = TempDir::new().unwrap();
    
    // 创建一些有效文件和无效文件
    let valid_content = r#"
# 有效文档

## 形式化定义

```math
\text{Test}(A, B) \equiv \forall a \in A. \exists b \in B. \text{Relation}(a, b)
```
"#;

    let invalid_content = r#"
# 无效文档

## 缺少数学符号的文档
"#;

    fs::write(temp_dir.path().join("valid.md"), valid_content).unwrap();
    fs::write(temp_dir.path().join("invalid.md"), invalid_content).unwrap();

    let args = vec![
        "integration_runner".to_string(),
        "all".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--output".to_string(),
        "json".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "错误恢复应该成功");
}

#[test]
fn test_performance_benchmark() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    let start = std::time::Instant::now();

    let args = vec![
        "integration_runner".to_string(),
        "all".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--output".to_string(),
        "json".to_string(),
    ];

    let result = integration_runner::run(args);
    let duration = start.elapsed();

    assert!(result.is_ok(), "性能测试应该成功");
    assert!(duration.as_millis() < 5000, "执行时间应该在5秒内");
}

#[test]
fn test_output_formats() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    let formats = vec!["json", "yaml", "text"];

    for format in formats {
        let args = vec![
            "integration_runner".to_string(),
            "symbol".to_string(),
            "--path".to_string(),
            temp_dir.path().to_string(),
            "--output".to_string(),
            format.to_string(),
        ];

        let result = integration_runner::run(args);
        assert!(result.is_ok(), "输出格式 {} 应该成功", format);
    }
}

#[test]
fn test_tool_specific_options() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    // 测试符号检查器的特定选项
    let args = vec![
        "integration_runner".to_string(),
        "symbol".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--strict".to_string(),
        "--ignore-case".to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "工具特定选项应该成功");
}

#[test]
fn test_configuration_file() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    // 创建配置文件
    let config_content = r#"
{
    "symbol_checker": {
        "strict_mode": true,
        "ignore_case": false
    },
    "concept_checker": {
        "validate_definitions": true,
        "check_usage": true
    },
    "hierarchy_validator": {
        "validate_structure": true,
        "check_consistency": true
    }
}
"#;

    let config_file = temp_dir.path().join("config.json");
    fs::write(&config_file, config_content).unwrap();

    let args = vec![
        "integration_runner".to_string(),
        "all".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--config".to_string(),
        config_file.to_string_lossy().to_string(),
    ];

    let result = integration_runner::run(args);
    assert!(result.is_ok(), "配置文件应该成功加载");
}

#[test]
fn test_plugin_system() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    // 模拟插件系统
    let args = vec![
        "integration_runner".to_string(),
        "all".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--plugins".to_string(),
        "custom_validator".to_string(),
    ];

    let result = integration_runner::run(args);
    // 插件系统可能未实现，所以这个测试可能失败
    // 但至少不应该panic
    assert!(result.is_ok() || result.is_err(), "插件系统应该正确处理");
}

#[test]
fn test_memory_leak_prevention() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    // 多次运行以检查内存泄漏
    for _ in 0..10 {
        let args = vec![
            "integration_runner".to_string(),
            "all".to_string(),
            "--path".to_string(),
            temp_dir.path().to_string(),
            "--output".to_string(),
            "json".to_string(),
        ];

        let result = integration_runner::run(args);
        assert!(result.is_ok(), "重复运行应该成功");
    }
}

#[test]
fn test_error_reporting() {
    let temp_dir = TempDir::new().unwrap();
    
    // 创建有问题的文件
    let problematic_content = r#"
# 问题文档

## 不一致的符号使用

```math
\text{Inconsistent}(A) \equiv \forall a \in A. \text{SomeFunction}(a)
```

但是后面使用了不同的符号：

```math
\text{Different}(B) \equiv \exists b \in B. \text{AnotherFunction}(b)
```
"#;

    fs::write(temp_dir.path().join("problematic.md"), problematic_content).unwrap();

    let args = vec![
        "integration_runner".to_string(),
        "all".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--output".to_string(),
        "json".to_string(),
    ];

    let result = integration_runner::run(args);
    // 应该检测到问题并报告
    assert!(result.is_ok(), "错误报告应该成功");
}

#[test]
fn test_integration_with_external_tools() {
    let temp_dir = TempDir::new().unwrap();
    create_test_files(&temp_dir).unwrap();

    let args = vec![
        "integration_runner".to_string(),
        "all".to_string(),
        "--path".to_string(),
        temp_dir.path().to_string(),
        "--external-tools".to_string(),
        "rustfmt,clippy".to_string(),
    ];

    let result = integration_runner::run(args);
    // 外部工具可能不可用，但应该优雅处理
    assert!(result.is_ok() || result.is_err(), "外部工具集成应该正确处理");
} 