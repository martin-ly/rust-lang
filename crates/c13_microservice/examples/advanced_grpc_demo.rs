//! 高级gRPC功能演示
//!
//! 展示流式处理、批量操作、拦截器和中间件等高级功能
#[allow(unused_imports)]
use c13_microservice::grpc::{
    AdvancedUserService, AdvancedGrpcClient,
    BatchUserRequest, BatchUserResponse,
    UserOperation, OperationResult,
};
use c13_microservice::config::Config;
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    println!("🚀 高级gRPC功能演示");
    
    // 创建配置
    let _config = Config::default();
    
    // 演示1: 高级用户服务
    demo_advanced_user_service().await?;
    
    // 演示2: 流式处理
    demo_streaming_processing().await?;
    
    // 演示3: 批量操作
    demo_batch_operations().await?;
    
    // 演示4: 版本控制和乐观锁
    demo_version_control().await?;
    
    // 演示5: 服务指标和健康检查
    demo_metrics_and_health().await?;
    
    println!("✅ 所有演示完成！");
    Ok(())
}

/// 演示高级用户服务功能
async fn demo_advanced_user_service() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📋 演示1: 高级用户服务功能");
    
    let config = Config::default();
    let service = AdvancedUserService::new(config);
    
    // 创建用户
    println!("创建用户...");
    let user1 = service.create_user("张三".to_string(), "zhangsan@example.com".to_string()).await?;
    println!("✅ 创建用户: {} ({})", user1.name, user1.email);
    
    let user2 = service.create_user("李四".to_string(), "lisi@example.com".to_string()).await?;
    println!("✅ 创建用户: {} ({})", user2.name, user2.email);
    
    // 获取用户
    println!("获取用户...");
    let retrieved_user = service.get_user(&user1.id).await?;
    println!("✅ 获取用户: {} (版本: {})", retrieved_user.name, retrieved_user.version);
    
    // 更新用户
    println!("更新用户...");
    let updated_user = service.update_user(
        &user1.id,
        Some("张三（更新）".to_string()),
        Some("zhangsan.updated@example.com".to_string()),
        user1.version,
    ).await?;
    println!("✅ 更新用户: {} (版本: {})", updated_user.name, updated_user.version);
    
    // 删除用户
    println!("删除用户...");
    let deleted = service.delete_user(&user2.id).await?;
    println!("✅ 删除用户: {}", if deleted { "成功" } else { "失败" });
    
    Ok(())
}

/// 演示流式处理
async fn demo_streaming_processing() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📋 演示2: 流式处理功能");
    
    let config = Config::default();
    let service = AdvancedUserService::new(config);
    
    // 创建一些测试用户
    for i in 1..=10 {
        let name = format!("用户{}", i);
        let email = format!("user{}@example.com", i);
        service.create_user(name, email).await?;
    }
    
    println!("创建了10个测试用户，开始流式处理...");
    
    // 流式获取用户
    let mut stream = service.stream_users(3).await; // 每批3个用户
    let mut batch_count = 0;
    let mut total_users = 0;
    
    while let Some(batch) = stream.recv().await {
        batch_count += 1;
        total_users += batch.users.len();
        
        println!("📦 批次 {}: 收到 {} 个用户", batch.batch_id, batch.users.len());
        for user in &batch.users {
            println!("   - {} ({})", user.name, user.email);
        }
        
        // 模拟处理延迟
        sleep(Duration::from_millis(100)).await;
    }
    
    println!("✅ 流式处理完成: 总共 {} 个批次，{} 个用户", batch_count, total_users);
    
    Ok(())
}

/// 演示批量操作
async fn demo_batch_operations() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📋 演示3: 批量操作功能");
    
    let config = Config::default();
    let service = AdvancedUserService::new(config);
    
    // 创建批量操作请求
    let batch_request = BatchUserRequest {
        operations: vec![
            UserOperation::Create { 
                name: "批量用户1".to_string(), 
                email: "batch1@example.com".to_string() 
            },
            UserOperation::Create { 
                name: "批量用户2".to_string(), 
                email: "batch2@example.com".to_string() 
            },
            UserOperation::Create { 
                name: "批量用户3".to_string(), 
                email: "batch3@example.com".to_string() 
            },
        ],
        batch_id: "demo_batch_001".to_string(),
    };
    
    println!("执行批量操作: {} 个操作", batch_request.operations.len());
    
    let start = std::time::Instant::now();
    let response = service.batch_operation(batch_request).await?;
    let duration = start.elapsed();
    
    println!("✅ 批量操作完成:");
    println!("   - 批次ID: {}", response.batch_id);
    println!("   - 成功: {} 个", response.success_count);
    println!("   - 失败: {} 个", response.failure_count);
    println!("   - 耗时: {:?}", duration);
    
    // 显示详细结果
    for result in response.results {
        match result {
            OperationResult::Success { id, operation } => {
                println!("   ✅ 成功: {} - {}", id, operation);
            }
            OperationResult::Failure { id, operation, error } => {
                println!("   ❌ 失败: {} - {} - 错误: {}", id, operation, error);
            }
        }
    }
    
    Ok(())
}

/// 演示版本控制和乐观锁
async fn demo_version_control() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📋 演示4: 版本控制和乐观锁");
    
    let config = Config::default();
    let service = AdvancedUserService::new(config);
    
    // 创建用户
    let user = service.create_user("版本测试用户".to_string(), "version@example.com".to_string()).await?;
    println!("创建用户: {} (版本: {})", user.name, user.version);
    
    // 第一次更新 - 应该成功
    println!("第一次更新...");
    let updated_user1 = service.update_user(
        &user.id,
        Some("第一次更新".to_string()),
        None,
        user.version, // 使用正确的版本号
    ).await?;
    println!("✅ 第一次更新成功: {} (版本: {})", updated_user1.name, updated_user1.version);
    
    // 第二次更新 - 使用错误的版本号，应该失败
    println!("第二次更新（使用错误版本号）...");
    match service.update_user(
        &user.id,
        Some("第二次更新".to_string()),
        None,
        user.version, // 使用旧的版本号，应该失败
    ).await {
        Ok(_) => println!("❌ 意外成功：版本控制未生效"),
        Err(e) => println!("✅ 版本冲突检测成功: {}", e),
    }
    
    // 第三次更新 - 使用正确的版本号，应该成功
    println!("第三次更新（使用正确版本号）...");
    let updated_user3 = service.update_user(
        &user.id,
        Some("第三次更新".to_string()),
        None,
        updated_user1.version, // 使用正确的版本号
    ).await?;
    println!("✅ 第三次更新成功: {} (版本: {})", updated_user3.name, updated_user3.version);
    
    Ok(())
}

/// 演示服务指标和健康检查
async fn demo_metrics_and_health() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📋 演示5: 服务指标和健康检查");
    
    let config = Config::default();
    let service = AdvancedUserService::new(config);
    
    // 执行一些操作来生成指标
    for i in 1..=5 {
        let name = format!("指标测试用户{}", i);
        let email = format!("metrics{}@example.com", i);
        service.create_user(name, email).await?;
    }
    
    // 获取服务指标
    let metrics = service.get_metrics();
    println!("📊 服务指标:");
    println!("   - 总请求数: {}", metrics.requests_total);
    println!("   - 成功请求数: {}", metrics.requests_success);
    println!("   - 失败请求数: {}", metrics.requests_failed);
    println!("   - 平均响应时间: {:?}", metrics.avg_response_time);
    
    // 健康检查
    let health = service.health_check().await?;
    println!("🏥 健康检查:");
    println!("   - 状态: {}", health.status);
    println!("   - 用户数量: {}", health.user_count);
    println!("   - 运行时间: {:?}", health.uptime);
    println!("   - 版本: {}", health.version);
    
    Ok(())
}

/// 演示gRPC客户端功能
#[allow(unused)]
async fn demo_grpc_client() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📋 演示6: gRPC客户端功能");
    
    // 注意：这里需要实际的gRPC服务器运行
    // 由于演示环境的限制，这里只展示客户端创建
    match AdvancedGrpcClient::new("http://localhost:50051").await {
        Ok(mut client) => {
            println!("✅ gRPC客户端创建成功");
            
            // 创建用户
            let user = client.create_user("客户端用户".to_string(), "client@example.com".to_string()).await?;
            println!("✅ 通过客户端创建用户: {}", user.name);
            
            // 流式获取用户
            let mut stream = client.stream_users(2).await?;
            println!("📦 开始流式获取用户...");
            
            while let Some(batch) = stream.recv().await {
                println!("   批次 {}: {} 个用户", batch.batch_id, batch.users.len());
            }
            
            // 批量操作
            let batch_request = BatchUserRequest {
                operations: vec![
                    UserOperation::Create { 
                        name: "客户端批量用户".to_string(), 
                        email: "client.batch@example.com".to_string() 
                    },
                ],
                batch_id: "client_batch".to_string(),
            };
            
            let response = client.batch_operation(batch_request).await?;
            println!("✅ 客户端批量操作完成: 成功 {} 个", response.success_count);
        }
        Err(e) => {
            println!("⚠️  gRPC客户端创建失败（服务器未运行）: {}", e);
        }
    }
    
    Ok(())
}

/// 演示错误处理和容错
#[allow(unused)]
async fn demo_error_handling() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📋 演示7: 错误处理和容错");
    
    let config = Config::default();
    let service = AdvancedUserService::new(config);
    
    // 测试获取不存在的用户
    println!("测试获取不存在的用户...");
    match service.get_user("nonexistent_user_id").await {
        Ok(_) => println!("❌ 意外成功：应该返回错误"),
        Err(e) => println!("✅ 正确返回错误: {}", e),
    }
    
    // 测试删除不存在的用户
    println!("测试删除不存在的用户...");
    let deleted = service.delete_user("nonexistent_user_id").await?;
    println!("✅ 删除不存在用户返回: {}", deleted);
    
    // 测试版本冲突
    let user = service.create_user("冲突测试用户".to_string(), "conflict@example.com".to_string()).await?;
    
    println!("测试版本冲突...");
    match service.update_user(&user.id, Some("冲突更新".to_string()), None, 999).await {
        Ok(_) => println!("❌ 意外成功：版本冲突未检测到"),
        Err(e) => println!("✅ 版本冲突检测成功: {}", e),
    }
    
    Ok(())
}