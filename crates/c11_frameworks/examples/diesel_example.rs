// Diesel 示例
// 运行命令: cargo run --example diesel_example --features diesel

use serde::{Deserialize, Serialize};

// 注意：这个示例需要实际的数据库连接
// 在实际使用中，你需要：
// 1. 设置 DATABASE_URL 环境变量
// 2. 运行 diesel migration run
// 3. 确保数据库表已创建

#[derive(Serialize, Deserialize, Debug)]
pub struct User {
    pub id: i32,
    pub name: String,
    pub email: String,
    pub created_at: chrono::NaiveDateTime,
}

#[derive(Deserialize, Debug)]
pub struct NewUser {
    pub name: String,
    pub email: String,
}

// 模拟数据库操作（实际使用中需要真实的数据库连接）
fn simulate_diesel_operations() {
    println!("=== Diesel ORM 示例 ===");
    
    // 模拟创建用户
    let new_user = NewUser {
        name: "张三".to_string(),
        email: "zhangsan@example.com".to_string(),
    };
    
    println!("创建用户: {:?}", new_user);
    
    // 模拟查询用户
    let user = User {
        id: 1,
        name: "张三".to_string(),
        email: "zhangsan@example.com".to_string(),
        created_at: chrono::Utc::now().naive_utc(),
    };
    
    println!("查询到的用户: {:?}", user);
    
    // 模拟更新用户
    println!("更新用户 ID: 1, 新名称: 李四");
    
    // 模拟删除用户
    println!("删除用户 ID: 1");
    
    println!("\n=== 实际使用步骤 ===");
    println!("1. 设置环境变量: export DATABASE_URL=\"postgresql://user:password@localhost/dbname\"");
    println!("2. 创建迁移: diesel migration generate create_users");
    println!("3. 运行迁移: diesel migration run");
    println!("4. 使用 diesel_cli 生成 schema.rs");
    println!("5. 在代码中使用 diesel::prelude::* 和生成的 schema");
}

// 实际的数据库操作函数（需要真实的数据库连接）
#[allow(dead_code)]
fn real_database_operations() -> Result<(), Box<dyn std::error::Error>> {
    // 模拟数据库操作（实际使用中需要真实的数据库连接和schema）
    println!("模拟数据库操作:");
    
    // 模拟创建用户
    let new_user = NewUser {
        name: "张三".to_string(),
        email: "zhangsan@example.com".to_string(),
    };
    
    println!("模拟创建用户: {:?}", new_user);
    
    // 模拟查询用户
    let user = User {
        id: 1,
        name: "张三".to_string(),
        email: "zhangsan@example.com".to_string(),
        created_at: chrono::Utc::now().naive_utc(),
    };
    
    println!("模拟查询用户: {:?}", user);
    
    // 模拟更新用户
    println!("模拟更新用户 ID: 1, 新名称: 李四");
    
    // 模拟删除用户
    println!("模拟删除用户 ID: 1");
    
    Ok(())
}

fn main() {
    simulate_diesel_operations();
    
    // 如果有数据库连接，可以取消注释下面的代码
    // if let Err(e) = real_database_operations() {
    //     eprintln!("数据库操作错误: {}", e);
    // }
}
