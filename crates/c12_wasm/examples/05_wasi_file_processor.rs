//! # WASI 文件处理器示例
//! # WASI example
//! ## 📐 知识结构
//! ## 📐 structure
//! ## 📐 知识structure
//! ### 核心概念
//! ### core concept
//!   - **属性**: 文件系统访问、命令行参数、标准I/O
//!   - **attribute **: file system 、command parameter 、standard I/O
//! ### 思维导图
//! ###
//! WASI 文件处理器
//! WASI
//! ├── 文件读取
//! ├── file reading
//! │   └── 读取文件内容
//! │ └── inside
//! ├── 文件处理
//! ├──
//! ├── 文件Handle
//! │   ├── 统计信息
//! │ ├──
//! │   └── 文本转换
//! │ └── this conversion
//! │ └── 文thisconversion
//! └── 文件写入
//! └── file writing
//!     └── 写入结果
//!     └── result
//!
//! ## 编译方式
//! ## way
//! ## 编译way
//! ## way
//! # 添加 WASI 目标
//! # WASI goal
//! # 添加 WASI goal
//! # 编译示例
//! # example
//! # 编译Example of
//!
//! ## 运行方式
//! ## Run way
//! ```bash
//!
//! # 或使用 wasmtime 运行
//! # or wasmtime Run
//! ```
//!
//! ## 功能说明
//! ## functionality explain
//! 这个程序可以：
//! program can ：
//! 这个programcan：
//! - 读取文件内容
//! - inside
//! - 统计行数、单词数、字符数
//! - 、、
//! - 转换为大写或小写
//! - conversion as or
//! - 查找特定文本
//! - this
use std::io::{self, Write};
use std::{env, fs};

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
