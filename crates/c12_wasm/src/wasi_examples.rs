//! # WASI 应用示例
//!
//! 本模块展示了如何编写可以在本地操作系统上运行的 WASI 应用程序

use std::env;
use std::fs;
use std::io::{self, Read, Write};
use std::path::Path;

/// 文件操作示例
pub mod file_operations {
    use super::*;

    /// 读取文件内容
    ///
    /// # 参数
    /// - `path`: 文件路径
    ///
    /// # 返回值
    /// 返回文件内容，如果文件不存在或读取失败则返回错误信息
    ///
    /// # 使用示例
    /// ```bash
    /// wasmedge your_app.wasm read_file.txt
    /// ```
    pub fn read_file(path: &str) -> Result<String, String> {
        fs::read_to_string(path)
            .map_err(|e| format!("Error reading file {}: {}", path, e))
    }

    /// 写入文件内容
    ///
    /// # 参数
    /// - `path`: 文件路径
    /// - `content`: 要写入的内容
    ///
    /// # 返回值
    /// 成功返回 Ok(())，失败返回错误信息
    pub fn write_file(path: &str, content: &str) -> Result<(), String> {
        fs::write(path, content)
            .map_err(|e| format!("Error writing file {}: {}", path, e))
    }

    /// 复制文件
    ///
    /// # 参数
    /// - `src`: 源文件路径
    /// - `dst`: 目标文件路径
    ///
    /// # 返回值
    /// 成功返回 Ok(())，失败返回错误信息
    pub fn copy_file(src: &str, dst: &str) -> Result<(), String> {
        fs::copy(src, dst)
            .map_err(|e| format!("Error copying file from {} to {}: {}", src, dst, e))?;
        Ok(())
    }

    /// 列出目录内容
    ///
    /// # 参数
    /// - `dir`: 目录路径
    ///
    /// # 返回值
    /// 返回目录中所有文件的名称列表
    pub fn list_directory(dir: &str) -> Result<Vec<String>, String> {
        let entries = fs::read_dir(dir)
            .map_err(|e| format!("Error reading directory {}: {}", dir, e))?;

        let mut files = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|e| format!("Error reading entry: {}", e))?;
            let name = entry.file_name().into_string()
                .map_err(|_| "Invalid file name".to_string())?;
            files.push(name);
        }
        Ok(files)
    }
}

/// 命令行参数处理示例
pub mod cli_examples {
    use super::*;

    /// 获取命令行参数
    ///
    /// # 返回值
    /// 返回所有命令行参数的向量
    ///
    /// # 使用示例
    /// ```bash
    /// wasmedge your_app.wasm arg1 arg2 arg3
    /// ```
    pub fn get_args() -> Vec<String> {
        env::args().collect()
    }

    /// 获取环境变量
    ///
    /// # 参数
    /// - `key`: 环境变量名称
    ///
    /// # 返回值
    /// 返回环境变量的值，如果不存在则返回 None
    ///
    /// # 使用示例
    /// ```bash
    /// MY_VAR=hello wasmedge your_app.wasm
    /// ```
    pub fn get_env_var(key: &str) -> Option<String> {
        env::var(key).ok()
    }

    /// 获取当前工作目录
    ///
    /// # 返回值
    /// 返回当前工作目录的路径
    pub fn get_current_dir() -> Result<String, String> {
        env::current_dir()
            .map(|p| p.to_string_lossy().to_string())
            .map_err(|e| format!("Error getting current directory: {}", e))
    }
}

/// 简单的文本处理工具
pub mod text_processor {
    /// 统计文件中的行数
    ///
    /// # 参数
    /// - `content`: 文件内容
    ///
    /// # 返回值
    /// 返回行数
    pub fn count_lines(content: &str) -> usize {
        content.lines().count()
    }

    /// 统计文件中的单词数
    ///
    /// # 参数
    /// - `content`: 文件内容
    ///
    /// # 返回值
    /// 返回单词数
    pub fn count_words(content: &str) -> usize {
        content.split_whitespace().count()
    }

    /// 统计文件中的字符数
    ///
    /// # 参数
    /// - `content`: 文件内容
    ///
    /// # 返回值
    /// 返回字符数（包括空格）
    pub fn count_chars(content: &str) -> usize {
        content.chars().count()
    }

    /// 将文本转换为大写
    ///
    /// # 参数
    /// - `content`: 要转换的文本
    ///
    /// # 返回值
    /// 返回转换为大写的文本
    pub fn to_uppercase(content: &str) -> String {
        content.to_uppercase()
    }

    /// 将文本转换为小写
    ///
    /// # 参数
    /// - `content`: 要转换的文本
    ///
    /// # 返回值
    /// 返回转换为小写的文本
    pub fn to_lowercase(content: &str) -> String {
        content.to_lowercase()
    }
}

/// 主函数示例
///
/// 这是一个完整的 WASI 应用程序示例，展示了如何：
/// 1. 读取命令行参数
/// 2. 读取文件
/// 3. 处理文本
/// 4. 输出结果
///
/// # 使用方法
/// ```bash
/// # 编译
/// cargo build --target wasm32-wasi --release
///
/// # 运行
/// wasmedge --dir .:/app target/wasm32-wasi/release/your_app.wasm input.txt
/// ```
pub fn main_example() {
    // 获取命令行参数
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <filename>", args[0]);
        std::process::exit(1);
    }

    let filename = &args[1];

    // 读取文件
    match file_operations::read_file(filename) {
        Ok(content) => {
            println!("File: {}", filename);
            println!("Lines: {}", text_processor::count_lines(&content));
            println!("Words: {}", text_processor::count_words(&content));
            println!("Chars: {}", text_processor::count_chars(&content));
        }
        Err(e) => {
            eprintln!("Error: {}", e);
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_count_lines() {
        assert_eq!(text_processor::count_lines("line1\nline2\nline3"), 3);
    }

    #[test]
    fn test_count_words() {
        assert_eq!(text_processor::count_words("hello world"), 2);
    }

    #[test]
    fn test_to_uppercase() {
        assert_eq!(text_processor::to_uppercase("hello"), "HELLO");
    }
}
