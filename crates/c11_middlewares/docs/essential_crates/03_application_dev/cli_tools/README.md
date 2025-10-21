# CLI 工具开发

> **核心库**: clap, dialoguer, indicatif, console  
> **适用场景**: 命令行工具、交互式程序、进度显示

---

## 📋 核心库

| 库 | 用途 | 特点 | 推荐度 |
|-----|------|------|--------|
| **clap** | 参数解析 | 功能全面 | ⭐⭐⭐⭐⭐ |
| **dialoguer** | 交互输入 | 易用 | ⭐⭐⭐⭐⭐ |
| **indicatif** | 进度条 | 美观 | ⭐⭐⭐⭐⭐ |
| **console** | 终端控制 | 跨平台 | ⭐⭐⭐⭐ |

---

## 🎯 clap - 参数解析

```rust
use clap::Parser;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// 输入文件
    #[arg(short, long)]
    input: String,
    
    /// 输出文件
    #[arg(short, long, default_value = "output.txt")]
    output: String,
    
    /// 详细模式
    #[arg(short, long)]
    verbose: bool,
}

fn main() {
    let cli = Cli::parse();
    
    println!("Input: {}", cli.input);
    println!("Output: {}", cli.output);
    if cli.verbose {
        println!("Verbose mode enabled");
    }
}
```

---

## 💬 dialoguer - 交互输入

```rust
use dialoguer::{Input, Select, Confirm, MultiSelect};

fn main() {
    // 文本输入
    let name: String = Input::new()
        .with_prompt("Your name")
        .interact()
        .unwrap();
    
    // 选择
    let items = vec!["Option 1", "Option 2", "Option 3"];
    let selection = Select::new()
        .with_prompt("Choose")
        .items(&items)
        .interact()
        .unwrap();
    
    // 确认
    let confirmed = Confirm::new()
        .with_prompt("Continue?")
        .interact()
        .unwrap();
    
    println!("Name: {}, Selected: {}, Confirmed: {}", 
        name, items[selection], confirmed);
}
```

---

## 📊 indicatif - 进度条

```rust
use indicatif::{ProgressBar, ProgressStyle};
use std::time::Duration;

fn main() {
    let pb = ProgressBar::new(100);
    pb.set_style(ProgressStyle::default_bar()
        .template("[{elapsed_precise}] {bar:40.cyan/blue} {pos:>7}/{len:7} {msg}")
        .unwrap());
    
    for i in 0..100 {
        pb.inc(1);
        std::thread::sleep(Duration::from_millis(50));
    }
    pb.finish_with_message("Done!");
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
