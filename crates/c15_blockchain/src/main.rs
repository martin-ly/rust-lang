//! # 区块链应用主程序
//!
//! 展示 Rust 1.89 特性在区块链开发中的应用
//! Demonstrates the application of Rust 1.89 features in blockchain development

mod cryptography;
mod network;
mod simple_blockchain;
mod smart_contract;
mod tools;
mod types;

use simple_blockchain::*;
use std::io::{self, Write};

fn main() {
    println!("🚀 区块链应用演示 - Rust 1.89 特性展示");
    println!("🚀 Blockchain Application Demo - Rust 1.89 Features Showcase");
    println!();

    // 演示 Rust 1.89 特性
    demonstrate_rust_189_features();

    // 交互式区块链演示
    interactive_blockchain_demo();
}

/// 演示 Rust 1.89 特性
/// Demonstrate Rust 1.89 features
fn demonstrate_rust_189_features() {
    println!("📋 Rust 1.89 特性演示");
    println!("📋 Rust 1.89 Features Demo");
    println!();

    // 1. 常量泛型推断
    println!("1️⃣ 常量泛型推断 (Const Generic Inference)");
    let data = b"Hello, Blockchain!";
    let hash: BlockHash<32> = BlockHash::<32>::from_data(data);
    println!("   数据: {:?}", String::from_utf8_lossy(data));
    println!("   哈希: {}", hash.to_string());
    println!();

    // 2. 生命周期语法检查
    println!("2️⃣ 生命周期语法检查 (Lifetime Syntax Check)");
    let _blockchain = Blockchain::new(2);
    let transaction = Transaction::new("alice".to_string(), "bob".to_string(), 100);
    let validation_result = transaction.validate();
    println!("   交易验证结果: {:?}", validation_result.is_valid);
    if !validation_result.errors.is_empty() {
        println!("   错误: {:?}", validation_result.errors);
    }
    println!();

    // 3. Result::flatten 简化错误处理
    println!("3️⃣ Result::flatten 简化错误处理 (Result::flatten Error Handling)");
    let mut blockchain = Blockchain::new(1); // 低难度用于演示
    let transaction = Transaction::new("genesis".to_string(), "alice".to_string(), 100);

    match blockchain.add_transaction(transaction) {
        Ok(_) => println!("   ✅ 交易添加成功"),
        Err(e) => println!("   ❌ 交易添加失败: {}", e),
    }
    println!();

    // 4. 挖矿演示
    println!("4️⃣ 挖矿演示 (Mining Demo)");
    println!("   开始挖矿...");
    match blockchain.mine_pending_transactions("miner".to_string()) {
        Ok(_) => {
            println!("   ✅ 挖矿成功！");
            println!("   链长度: {}", blockchain.get_chain_length());
            println!("   Alice 余额: {}", blockchain.get_balance("alice"));
            println!("   Miner 余额: {}", blockchain.get_balance("miner"));
        }
        Err(e) => println!("   ❌ 挖矿失败: {}", e),
    }
    println!();

    // 5. 链验证
    println!("5️⃣ 链验证 (Chain Validation)");
    let is_valid = blockchain.is_valid_chain();
    println!(
        "   链是否有效: {}",
        if is_valid { "✅ 是" } else { "❌ 否" }
    );
    println!();
}

/// 交互式区块链演示
/// Interactive blockchain demo
fn interactive_blockchain_demo() {
    println!("🎮 交互式区块链演示");
    println!("🎮 Interactive Blockchain Demo");
    println!();

    let mut blockchain = Blockchain::new(2);

    loop {
        println!("请选择操作 (Please select an operation):");
        println!("1. 添加交易 (Add Transaction)");
        println!("2. 挖矿 (Mining)");
        println!("3. 查看余额 (Check Balance)");
        println!("4. 查看链信息 (View Chain Info)");
        println!("5. 退出 (Exit)");
        print!("请输入选择 (1-5): ");
        io::stdout().flush().unwrap();

        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        let choice = input.trim();

        match choice {
            "1" => add_transaction_interactive(&mut blockchain),
            "2" => mine_block_interactive(&mut blockchain),
            "3" => check_balance_interactive(&blockchain),
            "4" => view_chain_info(&blockchain),
            "5" => {
                println!("👋 再见！(Goodbye!)");
                break;
            }
            _ => println!("❌ 无效选择，请重新输入 (Invalid choice, please try again)"),
        }

        println!();
    }
}

/// 交互式添加交易
/// Interactive add transaction
fn add_transaction_interactive(blockchain: &mut Blockchain) {
    print!("请输入发送者地址: ");
    io::stdout().flush().unwrap();
    let mut sender = String::new();
    io::stdin().read_line(&mut sender).unwrap();
    let sender = sender.trim().to_string();

    print!("请输入接收者地址: ");
    io::stdout().flush().unwrap();
    let mut receiver = String::new();
    io::stdin().read_line(&mut receiver).unwrap();
    let receiver = receiver.trim().to_string();

    print!("请输入金额: ");
    io::stdout().flush().unwrap();
    let mut amount_str = String::new();
    io::stdin().read_line(&mut amount_str).unwrap();

    match amount_str.trim().parse::<u64>() {
        Ok(amount) => {
            let transaction = Transaction::new(sender, receiver, amount);
            match blockchain.add_transaction(transaction) {
                Ok(_) => println!("✅ 交易添加成功"),
                Err(e) => println!("❌ 交易添加失败: {}", e),
            }
        }
        Err(_) => println!("❌ 无效金额"),
    }
}

/// 交互式挖矿
/// Interactive mining
fn mine_block_interactive(blockchain: &mut Blockchain) {
    print!("请输入挖矿奖励地址: ");
    io::stdout().flush().unwrap();
    let mut reward_address = String::new();
    io::stdin().read_line(&mut reward_address).unwrap();
    let reward_address = reward_address.trim();

    println!("⛏️ 开始挖矿...");
    match blockchain.mine_pending_transactions(reward_address.to_string()) {
        Ok(_) => {
            println!("✅ 挖矿成功！");
            println!("   链长度: {}", blockchain.get_chain_length());
        }
        Err(e) => println!("❌ 挖矿失败: {}", e),
    }
}

/// 交互式查看余额
/// Interactive check balance
fn check_balance_interactive(blockchain: &Blockchain) {
    print!("请输入地址: ");
    io::stdout().flush().unwrap();
    let mut address = String::new();
    io::stdin().read_line(&mut address).unwrap();
    let address = address.trim();

    let balance = blockchain.get_balance(address);
    println!("💰 {} 的余额: {}", address, balance);
}

/// 查看链信息
/// View chain info
fn view_chain_info(blockchain: &Blockchain) {
    println!("📊 链信息 (Chain Info):");
    println!("   链长度: {}", blockchain.get_chain_length());
    println!("   难度: {}", blockchain.difficulty);
    println!("   待处理交易数: {}", blockchain.pending_transactions.len());

    if let Some(latest_block) = blockchain.get_latest_block() {
        println!("   最新区块索引: {}", latest_block.index);
        println!("   最新区块哈希: {}", latest_block.hash.to_string());
        println!("   最新区块交易数: {}", latest_block.transactions.len());
    }

    println!(
        "   链是否有效: {}",
        if blockchain.is_valid_chain() {
            "✅ 是"
        } else {
            "❌ 否"
        }
    );
}
