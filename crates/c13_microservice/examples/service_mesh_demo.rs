//! 服务网格功能演示程序
//!
//! 展示服务发现、负载均衡、熔断器和流量管理功能

use std::time::Duration;
use tokio::time::sleep;
use c13_microservice::service_mesh::{
    ServiceMeshManager, ServiceMeshConfig, ServiceInstance,
    DiscoveryConfig, RegistryConfig, LoadBalancerConfig, LoadBalancingStrategy,
    CircuitBreakerConfig, TrafficConfig, TrafficPolicy, RetryPolicy, TimeoutPolicy,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🌐 服务网格功能演示程序");
    println!("========================");

    // 创建服务网格配置
    let service_mesh_config = create_service_mesh_config();
    
    // 创建服务网格管理器
    let mut service_mesh = ServiceMeshManager::new(service_mesh_config);

    // 演示服务发现
    demo_service_discovery(&mut service_mesh).await?;

    // 演示负载均衡
    demo_load_balancing(&mut service_mesh).await?;

    // 演示熔断器
    demo_circuit_breaker(&mut service_mesh).await?;

    // 演示流量管理
    demo_traffic_management(&mut service_mesh).await?;

    // 获取服务网格统计信息
    let stats = service_mesh.get_stats();
    println!("\n📊 服务网格统计信息:");
    println!("  已注册服务数: {}", stats.registered_services);
    println!("  活跃熔断器数: {}", stats.active_circuit_breakers);
    println!("  负载均衡策略: {}", stats.load_balancer_strategy);
    println!("  流量策略数: {}", stats.traffic_policies);

    println!("\n✅ 服务网格功能演示完成！");
    Ok(())
}

/// 创建服务网格配置
fn create_service_mesh_config() -> ServiceMeshConfig {
    // 服务发现配置
    let discovery_config = DiscoveryConfig {
        registry: RegistryConfig {
            service_ttl: Duration::from_secs(300), // 5分钟
            heartbeat_interval: Duration::from_secs(30),
            max_instances_per_service: 100,
        },
        refresh_interval: Duration::from_secs(30),
        cache_ttl: Duration::from_secs(60),
    };

    // 负载均衡配置
    let load_balancer_config = LoadBalancerConfig {
        strategy: LoadBalancingStrategy::RoundRobin,
        health_check_interval: Duration::from_secs(30),
        max_retries: 3,
        retry_delay: Duration::from_millis(100),
    };

    // 熔断器配置
    let circuit_breaker_config = CircuitBreakerConfig {
        failure_threshold: 5,
        success_threshold: 3,
        timeout: Duration::from_secs(60),
        max_failures: 10,
        slow_call_threshold: Duration::from_secs(2),
        slow_call_threshold_percentage: 50.0,
    };

    // 流量配置
    let traffic_config = TrafficConfig {
        default_policy: TrafficPolicy {
            retry: RetryPolicy {
                max_attempts: 3,
                initial_delay: Duration::from_millis(100),
                max_delay: Duration::from_secs(5),
                backoff_multiplier: 2.0,
                jitter: true,
                retryable_errors: vec![
                    "timeout".to_string(),
                    "connection_error".to_string(),
                    "service_unavailable".to_string(),
                ],
            },
            timeout: TimeoutPolicy {
                timeout: Duration::from_secs(30),
                connection_timeout: Duration::from_secs(10),
                read_timeout: Duration::from_secs(30),
                write_timeout: Duration::from_secs(30),
            },
            rate_limit: Default::default(),
            circuit_breaker: None,
        },
        rules: Vec::new(),
        global_rate_limit: None,
    };

    ServiceMeshConfig {
        discovery: discovery_config,
        load_balancer: load_balancer_config,
        traffic: traffic_config,
        circuit_breaker: circuit_breaker_config,
    }
}

/// 演示服务发现
async fn demo_service_discovery(service_mesh: &mut ServiceMeshManager) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔍 服务发现演示");
    println!("================");

    // 注册多个服务实例
    let service_instances = vec![
        ServiceInstance::new(
            "user-service-1".to_string(),
            "user-service".to_string(),
            "localhost".to_string(),
            8081,
        ),
        ServiceInstance::new(
            "user-service-2".to_string(),
            "user-service".to_string(),
            "localhost".to_string(),
            8082,
        ),
        ServiceInstance::new(
            "order-service-1".to_string(),
            "order-service".to_string(),
            "localhost".to_string(),
            8083,
        ),
    ];

    for instance in service_instances {
        service_mesh.register_service(instance).await?;
    }

    println!("✅ 已注册服务实例");

    // 发现服务实例
    let user_services = service_mesh.discover_services("user-service").await?;
    println!("🔍 发现用户服务实例:");
    for service in &user_services {
        println!("  - {}: {}", service.id, service.get_address());
    }

    let order_services = service_mesh.discover_services("order-service").await?;
    println!("🔍 发现订单服务实例:");
    for service in &order_services {
        println!("  - {}: {}", service.id, service.get_address());
    }

    // 获取服务健康状态
    let user_health = service_mesh.get_service_health("user-service").await?;
    println!("🏥 用户服务健康状态:");
    for health in &user_health {
        println!("  - {}: {} (响应时间: {:?})", 
            health.service_id, 
            if health.healthy { "健康" } else { "不健康" },
            health.response_time
        );
    }

    Ok(())
}

/// 演示负载均衡
async fn demo_load_balancing(service_mesh: &mut ServiceMeshManager) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n⚖️ 负载均衡演示");
    println!("================");

    // 模拟多次服务调用，展示负载均衡效果
    println!("🔄 轮询负载均衡演示:");
    for i in 1..=6 {
        match service_mesh.select_instance("user-service").await {
            Ok(instance) => {
                println!("  请求 {} -> {}", i, instance.id);
            }
            Err(e) => {
                println!("  请求 {} -> 错误: {}", i, e);
            }
        }
        sleep(Duration::from_millis(100)).await;
    }

    // 展示连接统计
    let connection_stats = service_mesh.load_balancer.get_connection_stats();
    if !connection_stats.is_empty() {
        println!("📊 连接统计:");
        for (service_id, count) in connection_stats {
            println!("  {}: {} 连接", service_id, count);
        }
    }

    Ok(())
}

/// 演示熔断器
async fn demo_circuit_breaker(service_mesh: &mut ServiceMeshManager) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔧 熔断器演示");
    println!("==============");

    // 添加熔断器配置
    let circuit_breaker_config = CircuitBreakerConfig {
        failure_threshold: 3,
        success_threshold: 2,
        timeout: Duration::from_secs(30),
        max_failures: 5,
        slow_call_threshold: Duration::from_secs(1),
        slow_call_threshold_percentage: 50.0,
    };

    service_mesh.add_circuit_breaker("user-service-1".to_string(), circuit_breaker_config);

    // 模拟服务调用
    println!("🔄 模拟服务调用:");

    // 成功的调用
    for _i in 1..=3 {
        let result = service_mesh.call_service("user-service", |instance| {
            let instance_id = instance.id.clone();
            async move {
                println!("   调用 {} (成功)", instance_id);
                Ok(format!("响应来自 {}", instance_id))
            }
        }).await;

        match result {
            Ok(response) => println!("   ✅ 成功: {}", response),
            Err(e) => println!("   ❌ 失败: {}", e),
        }
        sleep(Duration::from_millis(100)).await;
    }

    // 模拟失败的调用
    println!("💥 模拟失败调用:");
    for _i in 1..=5 {
        let result: Result<String, c13_microservice::service_mesh::ServiceMeshError> = service_mesh.call_service("user-service", |instance| {
            let instance_id = instance.id.clone();
            async move {
                println!("   调用 {} (失败)", instance_id);
                Err(c13_microservice::service_mesh::ServiceMeshError::ServiceTimeout)
            }
        }).await;

        match result {
            Ok(response) => println!("   ✅ 成功: {}", response),
            Err(e) => println!("   ❌ 失败: {}", e),
        }
        sleep(Duration::from_millis(100)).await;
    }

    // 展示熔断器状态
    if let Some(circuit_breaker) = service_mesh.circuit_breakers.get("user-service-1") {
        let stats = circuit_breaker.get_stats();
        println!("📊 熔断器统计:");
        println!("  状态: {}", stats.state);
        println!("  失败次数: {}", stats.failure_count);
        println!("  成功次数: {}", stats.success_count);
    }

    Ok(())
}

/// 演示流量管理
async fn demo_traffic_management(service_mesh: &mut ServiceMeshManager) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🚦 流量管理演示");
    println!("================");

    // 添加流量策略
    let traffic_policy = TrafficPolicy {
        retry: RetryPolicy {
            max_attempts: 3,
            initial_delay: Duration::from_millis(200),
            max_delay: Duration::from_secs(2),
            backoff_multiplier: 2.0,
            jitter: true,
            retryable_errors: vec![
                "timeout".to_string(),
                "connection_error".to_string(),
            ],
        },
        timeout: TimeoutPolicy {
            timeout: Duration::from_secs(10),
            connection_timeout: Duration::from_secs(5),
            read_timeout: Duration::from_secs(10),
            write_timeout: Duration::from_secs(10),
        },
        rate_limit: Default::default(),
        circuit_breaker: None,
    };

    service_mesh.traffic_manager.add_policy("user-service".to_string(), traffic_policy);

    println!("✅ 已添加流量策略");

    // 演示重试机制
    println!("🔄 重试机制演示:");
    for i in 1..=3 {
        let attempt = i;
        let result = service_mesh.traffic_manager.apply_policy("user-service", move || {
            Box::pin(async move {
                if attempt == 1 {
                    println!("   尝试 1: 模拟失败");
                    Err(c13_microservice::service_mesh::traffic_management::TrafficError::Timeout)
                } else {
                    println!("   尝试 {}: 成功", attempt);
                    Ok(format!("成功响应 {}", attempt))
                }
            })
        }).await;

        match result {
            Ok(response) => {
                println!("   ✅ 最终成功: {}", response);
                break;
            }
            Err(e) => {
                println!("   ❌ 失败: {}", e);
            }
        }
    }

    // 演示限流检查
    println!("🚦 限流检查演示:");
    for i in 1..=5 {
        match service_mesh.traffic_manager.check_rate_limit("user-service", &format!("client-{}", i)) {
            Ok(_) => println!("  请求 {} -> 允许", i),
            Err(e) => println!("  请求 {} -> 被限流: {}", i, e),
        }
    }

    println!("📊 流量策略统计:");
    println!("  策略数量: {}", service_mesh.traffic_manager.get_policy_count());

    Ok(())
}
