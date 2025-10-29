//! # WASI 应用程序示例
//!
//! 这是一个完整的 WASI 应用程序示例，展示了如何在本地操作系统上运行 WASM 程序

use std::env;
use std::fs;

fn main() {
    // 获取命令行参数
    let args: Vec<String> = env::args().collect();

    // 检查参数数量
    if args.len() < 2 {
        eprintln!("Usage: {} <filename>", args[0]);
        eprintln!("Example: {} input.txt", args[0]);
        std::process::exit(1);
    }

    // 读取文件名
    let filename = &args[1];

    // 读取文件内容
    match fs::read_to_string(filename) {
        Ok(content) => {
            // 处理文件内容
            let lines = content.lines().count();
            let words = content.split_whitespace().count();
            let chars = content.chars().count();

            // 输出统计信息
            println!("File: {}", filename);
            println!("Lines: {}", lines);
            println!("Words: {}", words);
            println!("Characters: {}", chars);
        }
        Err(e) => {
            eprintln!("Error reading file '{}': {}", filename, e);
            std::process::exit(1);
        }
    }
}
