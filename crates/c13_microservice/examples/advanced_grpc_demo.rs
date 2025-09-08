//! 高级gRPC服务演示
//! 
//! 展示认证、缓存、批量操作等高级gRPC服务功能

use c13_microservice::{
    grpc::advanced_services::{
        AdvancedGrpcService, AuthService, CacheService, BatchService,
        BatchOperation,
    },
    error::Result,
};
use tracing::info;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    info!("🚀 启动高级gRPC服务演示");
    
    // 创建高级gRPC服务
    let grpc_service = AdvancedGrpcService::new();
    
    // 启动服务
    grpc_service.start().await?;
    
    // 演示认证服务
    demo_auth_service(&grpc_service.auth_service).await?;
    
    // 演示缓存服务
    demo_cache_service(&grpc_service.cache_service).await?;
    
    // 演示批量操作服务
    demo_batch_service(&grpc_service.batch_service).await?;
    
    // 演示健康检查
    demo_health_check(&grpc_service).await?;
    
    info!("✅ 高级gRPC服务演示完成");
    Ok(())
}

/// 演示认证服务
async fn demo_auth_service(auth_service: &AuthService) -> Result<()> {
    info!("🔐 演示认证服务");
    
    // 用户登录
    let token = auth_service.login("alice".to_string(), "password123".to_string()).await?;
    info!("用户登录成功，获得token: {}", token.token);
    
    // 验证token
    let validated_token = auth_service.validate_token(&token.token).await?;
    info!("Token验证成功，用户ID: {}", validated_token.user_id);
    
    // 获取用户档案
    let profile = auth_service.get_user_profile(&validated_token.user_id).await?;
    info!("用户档案: {:?}", profile);
    
    // 用户登出
    auth_service.logout(&token.token).await?;
    info!("用户登出成功");
    
    Ok(())
}

/// 演示缓存服务
async fn demo_cache_service(cache_service: &CacheService) -> Result<()> {
    info!("💾 演示缓存服务");
    
    // 设置缓存
    let key = "user:123";
    let value = b"{\"name\":\"Alice\",\"email\":\"alice@example.com\"}";
    cache_service.set(key.to_string(), value.to_vec(), 300).await?;
    info!("缓存设置成功: {} = {}", key, String::from_utf8_lossy(value));
    
    // 获取缓存
    if let Some(cached_value) = cache_service.get(key).await? {
        info!("缓存命中: {} = {}", key, String::from_utf8_lossy(&cached_value));
    }
    
    // 设置多个缓存项
    let cache_items = vec![
        ("session:abc", "{\"user_id\":\"123\",\"expires\":\"2024-12-31\"}"),
        ("config:app", "{\"version\":\"1.0.0\",\"debug\":false}"),
        ("stats:daily", "{\"visits\":1000,\"users\":500}"),
    ];
    
    for (key, value) in cache_items {
        cache_service.set(key.to_string(), value.as_bytes().to_vec(), 600).await?;
        info!("缓存设置: {} = {}", key, value);
    }
    
    // 删除缓存
    let deleted = cache_service.delete("session:abc").await?;
    info!("缓存删除结果: {}", deleted);
    
    Ok(())
}

/// 演示批量操作服务
async fn demo_batch_service(batch_service: &BatchService) -> Result<()> {
    info!("📦 演示批量操作服务");
    
    // 创建批量操作
    let operations = vec![
        BatchOperation {
            id: "".to_string(),
            operation_type: "create_user".to_string(),
            data: b"{\"name\":\"Bob\",\"email\":\"bob@example.com\"}".to_vec(),
            status: "".to_string(),
            created_at: 0,
            completed_at: None,
        },
        BatchOperation {
            id: "".to_string(),
            operation_type: "update_user".to_string(),
            data: b"{\"id\":\"123\",\"name\":\"Bob Updated\"}".to_vec(),
            status: "".to_string(),
            created_at: 0,
            completed_at: None,
        },
        BatchOperation {
            id: "".to_string(),
            operation_type: "delete_user".to_string(),
            data: b"{\"id\":\"456\"}".to_vec(),
            status: "".to_string(),
            created_at: 0,
            completed_at: None,
        },
    ];
    
    let batch_id = batch_service.create_batch(operations).await?;
    info!("批量操作创建成功，批次ID: {}", batch_id);
    
    // 检查批量操作状态
    let status = batch_service.get_batch_status(&batch_id).await?;
    info!("批量操作状态: {:?}", status);
    
    // 执行批量操作
    let result = batch_service.execute_batch(&batch_id).await?;
    info!("批量操作执行完成:");
    info!("  总操作数: {}", result.total_operations);
    info!("  成功数: {}", result.success_count);
    info!("  失败数: {}", result.failure_count);
    
    if !result.errors.is_empty() {
        info!("错误信息:");
        for error in result.errors {
            info!("  {}", error);
        }
    }
    
    Ok(())
}

/// 演示健康检查
async fn demo_health_check(grpc_service: &AdvancedGrpcService) -> Result<()> {
    info!("🏥 演示健康检查");
    
    let health_status = grpc_service.health_check().await?;
    info!("服务健康状态:");
    info!("  状态: {}", health_status.status);
    info!("  缓存条目数: {}", health_status.cache_entries);
    info!("  活跃token数: {}", health_status.active_tokens);
    info!("  待处理操作数: {}", health_status.pending_operations);
    info!("  检查时间: {}", health_status.timestamp);
    
    Ok(())
}
