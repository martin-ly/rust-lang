// CLI 示例
// 运行命令: cargo run --example cli_example --features clap

use clap::{Args, Parser, Subcommand};

#[derive(Parser)]
#[command(name = "rust-frameworks-cli")]
#[command(about = "Rust框架生态系统CLI示例")]
#[command(version = "1.0")]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    #[arg(short, long, global = true)]
    verbose: bool,
}

#[derive(Subcommand)]
enum Commands {
    /// 用户管理
    User {
        #[command(subcommand)]
        action: UserAction,
    },
    /// 系统信息
    System,
    /// 框架信息
    Framework {
        #[command(subcommand)]
        action: FrameworkAction,
    },
}

#[derive(Subcommand)]
enum UserAction {
    /// 创建新用户
    Create(CreateUserArgs),
    /// 列出所有用户
    List,
    /// 删除用户
    Delete(DeleteUserArgs),
}

#[derive(Subcommand)]
enum FrameworkAction {
    /// 显示Web框架信息
    Web,
    /// 显示数据库框架信息
    Database,
    /// 显示所有框架信息
    All,
}

#[derive(Args)]
struct CreateUserArgs {
    /// 用户名
    #[arg(short, long)]
    name: String,

    /// 邮箱地址
    #[arg(short, long)]
    email: String,

    /// 年龄
    #[arg(short, long, default_value_t = 18)]
    age: u8,
}

#[derive(Args)]
struct DeleteUserArgs {
    /// 用户ID
    #[arg(short, long)]
    id: u32,

    /// 确认删除
    #[arg(short, long)]
    force: bool,
}

fn main() {
    let cli = Cli::parse();

    if cli.verbose {
        println!("详细模式已启用");
    }

    match &cli.command {
        Commands::User { action } => match action {
            UserAction::Create(args) => {
                println!("创建用户:");
                println!("  姓名: {}", args.name);
                println!("  邮箱: {}", args.email);
                println!("  年龄: {}", args.age);
            }
            UserAction::List => {
                println!("用户列表:");
                println!("  1. 张三 (zhangsan@example.com)");
                println!("  2. 李四 (lisi@example.com)");
                println!("  3. 王五 (wangwu@example.com)");
            }
            UserAction::Delete(args) => {
                if args.force {
                    println!("强制删除用户 ID: {}", args.id);
                } else {
                    println!("删除用户 ID: {} (使用 --force 确认删除)", args.id);
                }
            }
        },
        Commands::System => {
            println!("系统信息:");
            println!("  操作系统: {}", std::env::consts::OS);
            println!("  架构: {}", std::env::consts::ARCH);
            println!("  Rust版本: {}", "1.89.0");
        }
        Commands::Framework { action } => match action {
            FrameworkAction::Web => {
                println!("Web框架:");
                println!("  - Actix Web: 高性能Actor模型框架");
                println!("  - Axum: 现代异步优先框架");
                println!("  - Rocket: 安全易用框架");
                println!("  - Warp: 可组合过滤器框架");
            }
            FrameworkAction::Database => {
                println!("数据库框架:");
                println!("  - Diesel: 类型安全ORM");
                println!("  - SeaORM: 现代异步ORM");
                println!("  - SQLx: 编译时检查SQL工具包");
            }
            FrameworkAction::All => {
                println!("所有框架:");
                println!("  Web框架: Actix Web, Axum, Rocket, Warp");
                println!("  数据库: Diesel, SeaORM, SQLx");
                println!("  异步运行时: Tokio, async-std");
                println!("  序列化: Serde, Bincode, MessagePack");
                println!("  CLI: Clap, StructOpt");
                println!("  GUI: Tauri, Egui, Iced");
                println!("  测试: Criterion, Mockall, Proptest");
            }
        },
    }
}
