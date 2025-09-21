use c17_iot::{
    Network5GManager, Network5GManagerConfig, Network5GConfig, NetworkSliceConfig,
    NetworkConnection, Network5GStatus, QoSLevel
};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 5G网络集成演示开始");

    // 创建5G网络管理器配置
    let config = Network5GManagerConfig {
        enable_5g_network: true,
        default_qos_level: QoSLevel::VideoStreaming,
        custom_params: std::collections::HashMap::new(),
        enable_edge_computing: true,
        enable_network_slicing: true,
        max_connections: 1000,
        monitoring_interval: Duration::from_secs(5),
    };

    // 创建5G网络管理器
    let manager = Network5GManager::new(config);
    println!("✅ 5G网络管理器创建成功");

    // 创建5G网络配置
    let network_config = Network5GConfig {
        config_id: "5g_config_001".to_string(),
        network_type: c17_iot::Network5GType::EnhancedMobileBroadband,
        network_name: "5G网络配置".to_string(),
        carrier: "中国移动".to_string(),
        frequency_band: c17_iot::FrequencyBand::MidBand,
        network_parameters: c17_iot::NetworkParameters {
            bandwidth: 100,
            latency: 1,
            throughput: 1000,
            coverage_range: 1000.0,
            connection_density: 1000000,
            mobility_support: 500,
        },
        qos_config: c17_iot::QoSConfig {
            qos_level: QoSLevel::VideoStreaming,
            guaranteed_bit_rate: 100,
            maximum_bit_rate: 1000,
            latency_budget: 1,
            priority: 1,
            packet_loss_rate: 0.001,
        },
        security_config: c17_iot::Security5GConfig {
            encryption_algorithm: c17_iot::EncryptionAlgorithm::AES256,
            authentication_method: c17_iot::AuthenticationMethod::EAPAKA,
            key_management: c17_iot::KeyManagement::PublicKeyInfrastructure,
            security_policy: c17_iot::SecurityPolicy::Default,
            privacy_protection: c17_iot::PrivacyProtection::Full,
        },
        status: Network5GStatus::Connected,
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
    };

    // 创建网络连接
    let connection = NetworkConnection {
        connection_id: "conn_001".to_string(),
        network_config_id: "5g_config_001".to_string(),
        device_id: "device_001".to_string(),
        connection_status: Network5GStatus::Connected,
        connection_parameters: c17_iot::ConnectionParameters {
            signal_strength: -70,
            signal_to_noise_ratio: 20.0,
            latency: 1,
            throughput: 100,
            packet_loss_rate: 0.001,
        },
        connected_at: chrono::Utc::now(),
        last_activity: chrono::Utc::now(),
    };

    // 创建网络切片配置
    let slice_config = NetworkSliceConfig {
        slice_id: "slice_001".to_string(),
        slice_name: "切片_001".to_string(),
        slice_type: c17_iot::SliceType::EMBB,
        service_type: c17_iot::ServiceType::MobileBroadband,
        resource_allocation: c17_iot::ResourceAllocation {
            cpu_allocation: 20.0,
            memory_allocation: 25.0,
            bandwidth_allocation: 30.0,
            storage_allocation: 15.0,
            network_allocation: 10.0,
        },
        isolation_level: c17_iot::IsolationLevel::Logical,
        status: c17_iot::SliceStatus::Active,
        created_at: chrono::Utc::now(),
    };

    // 创建网络配置
    manager.create_network_config(network_config.clone()).await?;
    println!("✅ 网络配置创建成功: {}", network_config.config_id);

    // 启动网络监控
    let manager_arc = std::sync::Arc::new(manager);
    let manager_arc_clone = manager_arc.clone();
    manager_arc_clone.start_network_monitoring().await;
    println!("✅ 网络监控启动成功");

    // 创建网络切片
    manager_arc.create_slice_config(slice_config.clone()).await?;
    println!("✅ 网络切片创建成功: {}", slice_config.slice_name);

    // 模拟网络活动
    for i in 1..=5 {
        println!("\n📊 网络活动模拟 - 第{}轮", i);
        
        // 更新连接状态
        let mut updated_connection = connection.clone();
        updated_connection.connection_parameters.signal_strength = -70 + (i * 2);
        updated_connection.connection_parameters.throughput = 100 + (i as u32 * 10);
        updated_connection.last_activity = chrono::Utc::now();
        
        println!("  📡 连接状态更新: 信号强度 {} dBm, 吞吐量 {} Mbps", 
                updated_connection.connection_parameters.signal_strength,
                updated_connection.connection_parameters.throughput);

        // 更新切片状态
        let mut updated_slice = slice_config.clone();
        updated_slice.resource_allocation.bandwidth_allocation = 30.0 + (i as f64 * 5.0);
        
        println!("  🔧 切片状态更新: 带宽分配 {:.1}%", 
                updated_slice.resource_allocation.bandwidth_allocation);

        // 获取网络统计信息
        let stats = manager_arc.get_stats().await;
        println!("  📈 网络统计: 连接数 {}, 切片数 {}", 
                stats.total_network_configs, stats.total_slices);

        sleep(Duration::from_secs(2)).await;
    }

    // 获取最终统计信息
    let final_stats = manager_arc.get_stats().await;
    println!("\n📊 最终网络统计信息:");
    println!("  🔗 总网络配置数: {}", final_stats.total_network_configs);
    println!("  🔧 总切片数: {}", final_stats.total_slices);
    println!("  ⚡ 平均延迟: {:.1} ms", final_stats.avg_latency);
    println!("  🔒 活跃连接数: {}", final_stats.active_connections);
    println!("  🌐 边缘计算配置数: {}", final_stats.total_edge_configs);

    println!("✅ 网络监控停止成功");

    println!("\n🎉 5G网络集成演示完成！");
    Ok(())
}
