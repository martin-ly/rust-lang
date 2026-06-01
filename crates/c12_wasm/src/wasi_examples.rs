//! # WASI 应用示例
//! # WASI application example
use std::io::{self, Read, Write};
use std::path::Path;
use std::{env, fs};

/// 文件操作示例
/// file operation example
pub mod file_operations {
    use super::*;

    /// 读取文件内容
    /// inside
    /// # 参数
    /// # parameter
    /// - `path`: 文件路径
    /// - `path`:
    /// # 返回值
    /// # return value
    /// 返回文件内容，如果文件不存在或读取失败则返回错误信息
    /// inside ，if in or error message
    /// # 使用示例
    /// # example
    /// wasmedge your_app.wasm read_file.txt
    /// ```
    pub fn read_file(path: &str) -> Result<String, String> {
        fs::read_to_string(path).map_err(|e| format!("Error reading file {}: {}", path, e))
    }

    /// 写入文件内容
    /// inside
    /// # 参数
    /// # parameter
    /// - `path`: 文件路径
    /// - `path`:
    /// # 返回值
    /// # return value
    /// 成功返回 Ok(())，失败返回错误信息
    /// Ok(())，error message
    /// 成功Return Ok(())，失败Returnerror message
    pub fn write_file(path: &str, content: &str) -> Result<(), String> {
        fs::write(path, content).map_err(|e| format!("Error writing file {}: {}", path, e))
    }

    /// 复制文件
    /// # 参数
    /// # parameter
    /// - `src`: 源文件路径
    /// - `src`:
    /// - `dst`: 目标文件路径
    /// - `dst`: goal
    /// # 返回值
    /// # return value
    /// 成功返回 Ok(())，失败返回错误信息
    /// Ok(())，error message
    /// 成功Return Ok(())，失败Returnerror message
    pub fn copy_file(src: &str, dst: &str) -> Result<(), String> {
        fs::copy(src, dst)
            .map_err(|e| format!("Error copying file from {} to {}: {}", src, dst, e))?;
        Ok(())
    }

    /// 列出目录内容
    /// inside
    /// # 参数
    /// # parameter
    /// - `dir`: 目录路径
    /// - `dir`:
    /// # 返回值
    /// # return value
    /// 返回目录中所有文件的名称列表
    /// in all
    pub fn list_directory(dir: &str) -> Result<Vec<String>, String> {
        let entries =
            fs::read_dir(dir).map_err(|e| format!("Error reading directory {}: {}", dir, e))?;

        let mut files = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|e| format!("Error reading entry: {}", e))?;
            let name = entry
                .file_name()
                .into_string()
                .map_err(|_| "Invalid file name".to_string())?;
            files.push(name);
        }
        Ok(files)
    }
}

/// 命令行参数处理示例
/// command parameter example
pub mod cli_examples {
    use super::*;

    /// 获取命令行参数
    /// command parameter
    /// # 返回值
    /// # return value
    /// 返回所有命令行参数的向量
    /// all command parameter
    /// # 使用示例
    /// # example
    /// wasmedge your_app.wasm arg1 arg2 arg3
    /// ```
    pub fn get_args() -> Vec<String> {
        env::args().collect()
    }

    /// 获取环境变量
    /// environment variable
    /// # 参数
    /// # parameter
    /// - `key`: 环境变量名称
    /// - `key`: environment variable
    /// # 返回值
    /// # return value
    /// # 使用示例
    /// # example
    /// MY_VAR=hello wasmedge your_app.wasm
    /// ```
    pub fn get_env_var(key: &str) -> Option<String> {
        env::var(key).ok()
    }

    /// 获取当前工作目录
    /// when before
    /// # 返回值
    /// # return value
    /// 返回当前工作目录的路径
    /// when before
    pub fn get_current_dir() -> Result<String, String> {
        env::current_dir()
            .map(|p| p.to_string_lossy().to_string())
            .map_err(|e| format!("Error getting current directory: {}", e))
    }
}

/// 简单的文本处理工具
/// simple this tool
pub mod text_processor {
    /// 统计文件中的行数
    /// in
    /// # 参数
    /// # parameter
    /// - `content`: 文件内容
    /// - `content`: inside
    /// # 返回值
    /// # return value
    /// 返回行数
    pub fn count_lines(content: &str) -> usize {
        content.lines().count()
    }

    /// 统计文件中的单词数
    /// in
    /// # 参数
    /// # parameter
    /// - `content`: 文件内容
    /// - `content`: inside
    /// # 返回值
    /// # return value
    /// 返回单词数
    pub fn count_words(content: &str) -> usize {
        content.split_whitespace().count()
    }

    /// 统计文件中的字符数
    /// in
    /// # 参数
    /// # parameter
    /// - `content`: 文件内容
    /// - `content`: inside
    /// # 返回值
    /// # return value
    /// 返回字符数（包括空格）
    /// （）
    pub fn count_chars(content: &str) -> usize {
        content.chars().count()
    }

    /// 将文本转换为大写
    /// will this conversion as
    /// # 参数
    /// # parameter
    /// # 返回值
    /// # return value
    /// 返回转换为大写的文本
    /// conversion as this
    pub fn to_uppercase(content: &str) -> String {
        content.to_uppercase()
    }

    /// 将文本转换为小写
    /// will this conversion as
    /// # 参数
    /// # parameter
    /// # 返回值
    /// # return value
    /// 返回转换为小写的文本
    /// conversion as this
    pub fn to_lowercase(content: &str) -> String {
        content.to_lowercase()
    }
}

/// 主函数示例
/// Main function example
/// 1. 读取命令行参数
/// 1. command parameter
/// 2. 读取文件
/// 2.
/// 3. 处理文本
/// 3. this
/// 4. 输出结果
/// 4. result
/// # 使用方法
/// # method
/// # 编译
/// #
/// # 运行
/// # Run
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
