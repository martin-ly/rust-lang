//! gRPC客户端示例
//!
//! 展示如何使用gRPC客户端与服务进行通信。

use c13_microservice::grpc::GrpcClient;
use tracing::{error, info};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt().with_env_filter("info").init();

    info!("启动gRPC客户端示例");

    // 连接到gRPC服务器
    let server_url = "http://[::1]:50051"; // 默认gRPC端口
    let mut client = match GrpcClient::new(server_url).await {
        Ok(client) => {
            info!("成功连接到gRPC服务器: {}", server_url);
            client
        }
        Err(e) => {
            error!("无法连接到gRPC服务器: {}", e);
            info!("请确保gRPC服务器正在运行: cargo run --bin microservice-server -- grpc");
            return Ok(());
        }
    };

    // 健康检查
    match client.health_check().await {
        Ok(true) => info!("服务器健康检查通过"),
        Ok(false) => error!("服务器健康检查失败"),
        Err(e) => error!("健康检查错误: {}", e),
    }

    // 创建用户
    info!("创建用户...");
    match client
        .create_user("张三".to_string(), "zhangsan@example.com".to_string())
        .await
    {
        Ok(user) => {
            info!("用户创建成功: {:?}", user);

            // 获取用户
            info!("获取用户...");
            match client.get_user(user.id.clone()).await {
                Ok(retrieved_user) => {
                    info!("用户获取成功: {:?}", retrieved_user);

                    // 更新用户
                    info!("更新用户...");
                    match client
                        .update_user(
                            user.id.clone(),
                            Some("张三（更新）".to_string()),
                            Some("zhangsan_updated@example.com".to_string()),
                        )
                        .await
                    {
                        Ok(updated_user) => {
                            info!("用户更新成功: {:?}", updated_user);

                            // 列出用户
                            info!("列出用户...");
                            match client.list_users(1, 10).await {
                                Ok(users) => {
                                    info!("用户列表获取成功，共{}个用户:", users.len());
                                    for user in users {
                                        info!("  - {:?}", user);
                                    }

                                    // 删除用户
                                    info!("删除用户...");
                                    match client.delete_user(updated_user.id).await {
                                        Ok(true) => info!("用户删除成功"),
                                        Ok(false) => error!("用户删除失败"),
                                        Err(e) => error!("删除用户错误: {}", e),
                                    }
                                }
                                Err(e) => error!("列出用户错误: {}", e),
                            }
                        }
                        Err(e) => error!("更新用户错误: {}", e),
                    }
                }
                Err(e) => error!("获取用户错误: {}", e),
            }
        }
        Err(e) => error!("创建用户错误: {}", e),
    }

    info!("gRPC客户端示例完成");
    Ok(())
}
