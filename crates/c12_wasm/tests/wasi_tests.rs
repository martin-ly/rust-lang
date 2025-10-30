//! # WASI 功能测试
//!
//! 测试 WASI 相关的功能
//!
//! 注意：这些测试只能在 WASI 环境中运行
//! 运行方式：
//! ```bash
//! cargo test --target wasm32-wasi
//! ```

#[cfg(target_family = "wasm")]
use c12_wasm::wasi_examples::*;

#[cfg(target_family = "wasm")]
use std::fs;
#[cfg(target_family = "wasm")]
use std::io::Write;

// ============================================================================
// 文件操作测试
// ============================================================================

#[test]
#[cfg(target_family = "wasm")]
fn test_read_write_file() {
    use file_operations::*;

    let test_file = "test_temp_file.txt";
    let test_content = "Hello, WASI!";

    // 写入文件
    assert!(write_file(test_file, test_content).is_ok());

    // 读取文件
    let result = read_file(test_file);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), test_content);

    // 清理
    let _ = fs::remove_file(test_file);
}

#[test]
#[cfg(target_family = "wasm")]
fn test_copy_file() {
    use file_operations::*;

    let source_file = "test_source.txt";
    let dest_file = "test_dest.txt";
    let content = "Test content for copy";

    // 创建源文件
    assert!(write_file(source_file, content).is_ok());

    // 复制文件
    assert!(copy_file(source_file, dest_file).is_ok());

    // 验证目标文件
    let result = read_file(dest_file);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), content);

    // 清理
    let _ = fs::remove_file(source_file);
    let _ = fs::remove_file(dest_file);
}

#[test]
#[cfg(target_family = "wasm")]
fn test_read_nonexistent_file() {
    use file_operations::read_file;

    let result = read_file("nonexistent_file_12345.txt");
    assert!(result.is_err());
}

// ============================================================================
// 命令行参数测试
// ============================================================================

#[test]
#[cfg(target_family = "wasm")]
fn test_get_args() {
    use cli_examples::get_args;

    let args = get_args();
    // 至少应该有程序名称
    assert!(!args.is_empty());
}

#[test]
#[cfg(target_family = "wasm")]
fn test_get_current_dir() {
    use cli_examples::get_current_dir;

    let result = get_current_dir();
    assert!(result.is_ok());

    let dir = result.unwrap();
    assert!(!dir.is_empty());
}

// ============================================================================
// 文本处理测试
// ============================================================================

#[test]
#[cfg(target_family = "wasm")]
fn test_text_processor() {
    use file_operations::write_file;
    use text_processor::*;

    let test_file = "test_text_processor.txt";
    let content = "Line 1\nLine 2\nLine 3\n\nLine 5";

    // 创建测试文件
    assert!(write_file(test_file, content).is_ok());

    // 测试行数统计
    let lines = count_lines(test_file);
    assert!(lines.is_ok());
    assert_eq!(lines.unwrap(), 5);

    // 测试单词统计
    let words = count_words(test_file);
    assert!(words.is_ok());

    // 测试字符统计
    let chars = count_chars(test_file);
    assert!(chars.is_ok());

    // 清理
    let _ = fs::remove_file(test_file);
}

#[test]
#[cfg(target_family = "wasm")]
fn test_text_case_conversion() {
    use file_operations::write_file;
    use text_processor::*;

    let test_file = "test_case_conversion.txt";
    let content = "Hello World";

    // 创建测试文件
    assert!(write_file(test_file, content).is_ok());

    // 测试大写转换
    let upper = to_uppercase(test_file);
    assert!(upper.is_ok());
    assert_eq!(upper.unwrap(), "HELLO WORLD");

    // 测试小写转换
    let lower = to_lowercase(test_file);
    assert!(lower.is_ok());
    assert_eq!(lower.unwrap(), "hello world");

    // 清理
    let _ = fs::remove_file(test_file);
}

// ============================================================================
// 边界情况测试
// ============================================================================

#[test]
#[cfg(target_family = "wasm")]
fn test_empty_file() {
    use file_operations::*;
    use text_processor::*;

    let test_file = "test_empty.txt";

    // 创建空文件
    assert!(write_file(test_file, "").is_ok());

    // 测试读取
    let content = read_file(test_file);
    assert!(content.is_ok());
    assert_eq!(content.unwrap(), "");

    // 测试统计
    let lines = count_lines(test_file);
    assert!(lines.is_ok());
    assert_eq!(lines.unwrap(), 0);

    // 清理
    let _ = fs::remove_file(test_file);
}

#[test]
#[cfg(target_family = "wasm")]
fn test_large_content() {
    use file_operations::*;

    let test_file = "test_large.txt";
    // 创建一个较大的内容
    let content = "Hello World\n".repeat(1000);

    // 写入
    assert!(write_file(test_file, &content).is_ok());

    // 读取
    let result = read_file(test_file);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), content);

    // 清理
    let _ = fs::remove_file(test_file);
}

// ============================================================================
// 集成测试
// ============================================================================

#[test]
#[cfg(target_family = "wasm")]
fn test_file_processing_workflow() {
    use file_operations::*;
    use text_processor::*;

    let input_file = "test_workflow_input.txt";
    let output_file = "test_workflow_output.txt";
    let content = "hello world\nrust wasm\nwasi test";

    // 1. 写入原始文件
    assert!(write_file(input_file, content).is_ok());

    // 2. 读取并转换为大写
    let upper = to_uppercase(input_file);
    assert!(upper.is_ok());

    // 3. 写入输出文件
    assert!(write_file(output_file, &upper.unwrap()).is_ok());

    // 4. 验证输出
    let result = read_file(output_file);
    assert!(result.is_ok());
    assert!(result.unwrap().contains("HELLO WORLD"));

    // 5. 统计信息
    let lines = count_lines(output_file);
    assert!(lines.is_ok());
    assert_eq!(lines.unwrap(), 3);

    // 清理
    let _ = fs::remove_file(input_file);
    let _ = fs::remove_file(output_file);
}

// 为非 WASI 环境提供占位测试
#[test]
#[cfg(not(target_family = "wasm"))]
fn wasi_tests_skip_on_non_wasi() {
    // 这个测试在非 WASI 环境中会被跳过
    println!("WASI tests are only available when targeting wasm32-wasi");
    println!("Run with: cargo test --target wasm32-wasi");
}
