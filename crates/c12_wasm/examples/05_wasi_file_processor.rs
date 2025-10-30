//! # WASI 文件处理器示例
//!
//! 展示如何使用 WASI 创建可以在本地运行的命令行工具
//!
//! ## 编译方式
//!
//! ```bash
//! # 添加 WASI 目标
//! rustup target add wasm32-wasi
//!
//! # 编译示例
//! cargo build --example 05_wasi_file_processor --target wasm32-wasi --release
//! ```
//!
//! ## 运行方式
//!
//! ```bash
//! # 使用 WasmEdge 运行
//! wasmedge target/wasm32-wasi/release/examples/05_wasi_file_processor.wasm input.txt
//!
//! # 或使用 wasmtime 运行
//! wasmtime target/wasm32-wasi/release/examples/05_wasi_file_processor.wasm input.txt
//! ```
//!
//! ## 功能说明
//!
//! 这个程序可以：
//! - 读取文件内容
//! - 统计行数、单词数、字符数
//! - 转换为大写或小写
//! - 查找特定文本

use std::env;
use std::fs;
use std::io::{self, Write};

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        print_usage(&args[0]);
        std::process::exit(1);
    }

    let command = &args[1];

    match command.as_str() {
        "count" => {
            if args.len() < 3 {
                eprintln!("Error: Missing file path");
                eprintln!("Usage: {} count <file>", args[0]);
                std::process::exit(1);
            }
            count_file(&args[2]);
        }
        "uppercase" => {
            if args.len() < 3 {
                eprintln!("Error: Missing file path");
                std::process::exit(1);
            }
            uppercase_file(&args[2]);
        }
        "lowercase" => {
            if args.len() < 3 {
                eprintln!("Error: Missing file path");
                std::process::exit(1);
            }
            lowercase_file(&args[2]);
        }
        "search" => {
            if args.len() < 4 {
                eprintln!("Error: Missing file path or search term");
                eprintln!("Usage: {} search <file> <term>", args[0]);
                std::process::exit(1);
            }
            search_in_file(&args[2], &args[3]);
        }
        "cat" => {
            if args.len() < 3 {
                eprintln!("Error: Missing file path");
                std::process::exit(1);
            }
            cat_file(&args[2]);
        }
        "help" | "--help" | "-h" => {
            print_usage(&args[0]);
        }
        _ => {
            eprintln!("Error: Unknown command '{}'", command);
            print_usage(&args[0]);
            std::process::exit(1);
        }
    }
}

fn print_usage(program_name: &str) {
    println!("WASI File Processor - A command-line tool for text file processing");
    println!();
    println!("USAGE:");
    println!("    {} <COMMAND> [OPTIONS]", program_name);
    println!();
    println!("COMMANDS:");
    println!("    count <file>          Count lines, words, and characters in a file");
    println!("    uppercase <file>      Convert file content to uppercase");
    println!("    lowercase <file>      Convert file content to lowercase");
    println!("    search <file> <term>  Search for a term in the file");
    println!("    cat <file>            Display file contents");
    println!("    help                  Show this help message");
    println!();
    println!("EXAMPLES:");
    println!("    {} count input.txt", program_name);
    println!("    {} search data.txt 'hello'", program_name);
    println!("    {} uppercase input.txt", program_name);
}

fn read_file(path: &str) -> Result<String, io::Error> {
    fs::read_to_string(path)
}

fn count_file(path: &str) {
    match read_file(path) {
        Ok(content) => {
            let lines = content.lines().count();
            let words = content.split_whitespace().count();
            let chars = content.chars().count();
            let bytes = content.len();

            println!("File: {}", path);
            println!("  Lines:      {}", lines);
            println!("  Words:      {}", words);
            println!("  Characters: {}", chars);
            println!("  Bytes:      {}", bytes);
        }
        Err(e) => {
            eprintln!("Error reading file '{}': {}", path, e);
            std::process::exit(1);
        }
    }
}

fn uppercase_file(path: &str) {
    match read_file(path) {
        Ok(content) => {
            let uppercase = content.to_uppercase();
            println!("{}", uppercase);
        }
        Err(e) => {
            eprintln!("Error reading file '{}': {}", path, e);
            std::process::exit(1);
        }
    }
}

fn lowercase_file(path: &str) {
    match read_file(path) {
        Ok(content) => {
            let lowercase = content.to_lowercase();
            println!("{}", lowercase);
        }
        Err(e) => {
            eprintln!("Error reading file '{}': {}", path, e);
            std::process::exit(1);
        }
    }
}

fn search_in_file(path: &str, search_term: &str) {
    match read_file(path) {
        Ok(content) => {
            let mut found_count = 0;
            for (line_num, line) in content.lines().enumerate() {
                if line.contains(search_term) {
                    println!("{}:{}: {}", path, line_num + 1, line);
                    found_count += 1;
                }
            }

            if found_count == 0 {
                println!("No matches found for '{}' in '{}'", search_term, path);
            } else {
                println!();
                println!("Found {} match(es)", found_count);
            }
        }
        Err(e) => {
            eprintln!("Error reading file '{}': {}", path, e);
            std::process::exit(1);
        }
    }
}

fn cat_file(path: &str) {
    match read_file(path) {
        Ok(content) => {
            print!("{}", content);
            io::stdout().flush().unwrap();
        }
        Err(e) => {
            eprintln!("Error reading file '{}': {}", path, e);
            std::process::exit(1);
        }
    }
}
