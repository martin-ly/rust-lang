//! 高级协议演示示例
//! 
//! 展示如何使用c17_iot的高级协议功能进行现代IoT通信

use c17_iot::protocols::advanced_protocols::{
    AdvancedProtocolManager,
    AdvancedProtocolConfig,
    AdvancedProtocolType, 
    Message,
    MessageType, 
    AuthInfo,
};
use std::time::Duration;
use std::collections::HashMap;
//use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动高级协议演示...");

    println!("📊 开始演示各种高级IoT通信协议...");

    // 1. WebSocket协议演示
    println!("\n1️⃣ WebSocket协议演示");
    demo_websocket_protocol().await?;

    // 2. gRPC协议演示
    println!("\n2️⃣ gRPC协议演示");
    demo_grpc_protocol().await?;

    // 3. GraphQL协议演示
    println!("\n3️⃣ GraphQL协议演示");
    demo_graphql_protocol().await?;

    // 4. WebRTC协议演示
    println!("\n4️⃣ WebRTC协议演示");
    demo_webrtc_protocol().await?;

    // 5. AMQP协议演示
    println!("\n5️⃣ AMQP协议演示");
    demo_amqp_protocol().await?;

    // 6. Kafka协议演示
    println!("\n6️⃣ Kafka协议演示");
    demo_kafka_protocol().await?;

    // 7. NATS协议演示
    println!("\n7️⃣ NATS协议演示");
    demo_nats_protocol().await?;

    // 8. 协议性能对比
    println!("\n8️⃣ 协议性能对比");
    compare_protocol_performance().await?;

    println!("\n✅ 高级协议演示完成!");
    println!("🎯 演示展示了以下功能:");
    println!("  - 多种现代IoT通信协议");
    println!("  - 连接管理和状态监控");
    println!("  - 消息发送和接收");
    println!("  - 协议性能对比");
    println!("  - 错误处理和恢复");

    Ok(())
}

/// WebSocket协议演示
async fn demo_websocket_protocol() -> Result<(), Box<dyn std::error::Error>> {
    let config = AdvancedProtocolConfig {
        protocol_type: AdvancedProtocolType::WebSocket,
        server_url: "ws://localhost:8080".to_string(),
        port: 8080,
        connection_timeout: Duration::from_secs(10),
        read_timeout: Duration::from_secs(30),
        write_timeout: Duration::from_secs(30),
        reconnect_interval: Duration::from_secs(5),
        max_reconnect_attempts: 3,
        enable_ssl: false,
        auth_info: None,
        custom_config: HashMap::new(),
    };

    let manager = AdvancedProtocolManager::new(config);
    
    println!("  连接到WebSocket服务器...");
    manager.connect().await?;
    
    let status = manager.get_connection_status().await;
    println!("  连接状态: {:?}", status);
    
    // 发送消息
    let message = Message {
        id: uuid::Uuid::new_v4().to_string(),
        message_type: MessageType::Text("WebSocket测试消息".to_string()),
        timestamp: chrono::Utc::now(),
        sender: "demo_client".to_string(),
        receiver: None,
        topic: Some("test".to_string()),
        headers: HashMap::new(),
        payload: None,
    };
    
    println!("  发送WebSocket消息...");
    manager.send_message(message).await?;
    
    // 接收消息
    println!("  接收WebSocket消息...");
    let received_message = manager.receive_message().await?;
    println!("  收到消息: {:?}", received_message.message_type);
    
    // 获取统计信息
    let stats = manager.get_connection_stats().await;
    println!("  发送消息数: {}", stats.messages_sent);
    println!("  接收消息数: {}", stats.messages_received);
    
    manager.disconnect().await?;
    println!("  WebSocket连接已断开");
    
    Ok(())
}

/// gRPC协议演示
async fn demo_grpc_protocol() -> Result<(), Box<dyn std::error::Error>> {
    let config = AdvancedProtocolConfig {
        protocol_type: AdvancedProtocolType::GRPC,
        server_url: "grpc://localhost:50051".to_string(),
        port: 50051,
        connection_timeout: Duration::from_secs(10),
        read_timeout: Duration::from_secs(30),
        write_timeout: Duration::from_secs(30),
        reconnect_interval: Duration::from_secs(5),
        max_reconnect_attempts: 3,
        enable_ssl: true,
        auth_info: Some(AuthInfo {
            username: "grpc_user".to_string(),
            password: "grpc_pass".to_string(),
            token: Some("grpc_token_123".to_string()),
            api_key: None,
            cert_path: Some("/path/to/cert.pem".to_string()),
            key_path: Some("/path/to/key.pem".to_string()),
        }),
        custom_config: HashMap::new(),
    };

    let manager = AdvancedProtocolManager::new(config);
    
    println!("  连接到gRPC服务器...");
    manager.connect().await?;
    
    let status = manager.get_connection_status().await;
    println!("  连接状态: {:?}", status);
    
    // 发送gRPC消息
    let message = Message {
        id: uuid::Uuid::new_v4().to_string(),
        message_type: MessageType::Json(serde_json::json!({
            "service": "IoTService",
            "method": "GetDeviceData",
            "request": {
                "device_id": "device_001",
                "timestamp": chrono::Utc::now()
            }
        })),
        timestamp: chrono::Utc::now(),
        sender: "grpc_client".to_string(),
        receiver: None,
        topic: Some("iot_service".to_string()),
        headers: HashMap::new(),
        payload: None,
    };
    
    println!("  发送gRPC请求...");
    manager.send_message(message).await?;
    
    // 接收gRPC响应
    println!("  接收gRPC响应...");
    let response = manager.receive_message().await?;
    println!("  收到响应: {:?}", response.message_type);
    
    manager.disconnect().await?;
    println!("  gRPC连接已断开");
    
    Ok(())
}

/// GraphQL协议演示
async fn demo_graphql_protocol() -> Result<(), Box<dyn std::error::Error>> {
    let config = AdvancedProtocolConfig {
        protocol_type: AdvancedProtocolType::GraphQL,
        server_url: "http://localhost:4000/graphql".to_string(),
        port: 4000,
        connection_timeout: Duration::from_secs(10),
        read_timeout: Duration::from_secs(30),
        write_timeout: Duration::from_secs(30),
        reconnect_interval: Duration::from_secs(5),
        max_reconnect_attempts: 3,
        enable_ssl: false,
        auth_info: Some(AuthInfo {
            username: "graphql_user".to_string(),
            password: "graphql_pass".to_string(),
            token: Some("graphql_token_456".to_string()),
            api_key: None,
            cert_path: None,
            key_path: None,
        }),
        custom_config: HashMap::new(),
    };

    let manager = AdvancedProtocolManager::new(config);
    
    println!("  连接到GraphQL服务器...");
    manager.connect().await?;
    
    // 发送GraphQL查询
    let query = Message {
        id: uuid::Uuid::new_v4().to_string(),
        message_type: MessageType::Text(r#"
            query GetDevices {
                devices {
                    id
                    name
                    status
                    lastSeen
                    sensors {
                        id
                        type
                        value
                        timestamp
                    }
                }
            }
        "#.to_string()),
        timestamp: chrono::Utc::now(),
        sender: "graphql_client".to_string(),
        receiver: None,
        topic: Some("query".to_string()),
        headers: HashMap::new(),
        payload: None,
    };
    
    println!("  发送GraphQL查询...");
    manager.send_message(query).await?;
    
    // 接收GraphQL响应
    println!("  接收GraphQL响应...");
    let response = manager.receive_message().await?;
    println!("  收到响应: {:?}", response.message_type);
    
    manager.disconnect().await?;
    println!("  GraphQL连接已断开");
    
    Ok(())
}

/// WebRTC协议演示
async fn demo_webrtc_protocol() -> Result<(), Box<dyn std::error::Error>> {
    let config = AdvancedProtocolConfig {
        protocol_type: AdvancedProtocolType::WebRTC,
        server_url: "webrtc://localhost:8443".to_string(),
        port: 8443,
        connection_timeout: Duration::from_secs(15),
        read_timeout: Duration::from_secs(60),
        write_timeout: Duration::from_secs(60),
        reconnect_interval: Duration::from_secs(10),
        max_reconnect_attempts: 5,
        enable_ssl: true,
        auth_info: None,
        custom_config: HashMap::new(),
    };

    let manager = AdvancedProtocolManager::new(config);
    
    println!("  建立WebRTC连接...");
    manager.connect().await?;
    
    let status = manager.get_connection_status().await;
    println!("  连接状态: {:?}", status);
    
    // 发送实时数据
    let realtime_data = Message {
        id: uuid::Uuid::new_v4().to_string(),
        message_type: MessageType::Binary(vec![0x01, 0x02, 0x03, 0x04, 0x05]),
        timestamp: chrono::Utc::now(),
        sender: "webrtc_client".to_string(),
        receiver: None,
        topic: Some("realtime_data".to_string()),
        headers: HashMap::new(),
        payload: Some(vec![0x01, 0x02, 0x03, 0x04, 0x05]),
    };
    
    println!("  发送实时数据...");
    manager.send_message(realtime_data).await?;
    
    // 接收实时数据
    println!("  接收实时数据...");
    let received_data = manager.receive_message().await?;
    println!("  收到数据: {:?}", received_data.message_type);
    
    manager.disconnect().await?;
    println!("  WebRTC连接已断开");
    
    Ok(())
}

/// AMQP协议演示
async fn demo_amqp_protocol() -> Result<(), Box<dyn std::error::Error>> {
    let config = AdvancedProtocolConfig {
        protocol_type: AdvancedProtocolType::AMQP,
        server_url: "amqp://localhost:5672".to_string(),
        port: 5672,
        connection_timeout: Duration::from_secs(10),
        read_timeout: Duration::from_secs(30),
        write_timeout: Duration::from_secs(30),
        reconnect_interval: Duration::from_secs(5),
        max_reconnect_attempts: 3,
        enable_ssl: false,
        auth_info: Some(AuthInfo {
            username: "amqp_user".to_string(),
            password: "amqp_pass".to_string(),
            token: None,
            api_key: None,
            cert_path: None,
            key_path: None,
        }),
        custom_config: HashMap::new(),
    };

    let manager = AdvancedProtocolManager::new(config);
    
    println!("  连接到AMQP服务器...");
    manager.connect().await?;
    
    // 发送消息到队列
    let queue_message = Message {
        id: uuid::Uuid::new_v4().to_string(),
        message_type: MessageType::Structured(HashMap::from([
            ("device_id".to_string(), serde_json::Value::String("device_001".to_string())),
            ("sensor_data".to_string(), serde_json::Value::Object(serde_json::Map::new())),
            ("timestamp".to_string(), serde_json::Value::String(chrono::Utc::now().to_rfc3339())),
        ])),
        timestamp: chrono::Utc::now(),
        sender: "amqp_producer".to_string(),
        receiver: None,
        topic: Some("iot.sensor.data".to_string()),
        headers: HashMap::new(),
        payload: None,
    };
    
    println!("  发送消息到AMQP队列...");
    manager.send_message(queue_message).await?;
    
    // 从队列接收消息
    println!("  从AMQP队列接收消息...");
    let received_message = manager.receive_message().await?;
    println!("  收到消息: {:?}", received_message.message_type);
    
    manager.disconnect().await?;
    println!("  AMQP连接已断开");
    
    Ok(())
}

/// Kafka协议演示
async fn demo_kafka_protocol() -> Result<(), Box<dyn std::error::Error>> {
    let config = AdvancedProtocolConfig {
        protocol_type: AdvancedProtocolType::Kafka,
        server_url: "kafka://localhost:9092".to_string(),
        port: 9092,
        connection_timeout: Duration::from_secs(10),
        read_timeout: Duration::from_secs(30),
        write_timeout: Duration::from_secs(30),
        reconnect_interval: Duration::from_secs(5),
        max_reconnect_attempts: 3,
        enable_ssl: false,
        auth_info: None,
        custom_config: HashMap::from([
            ("bootstrap_servers".to_string(), "localhost:9092".to_string()),
            ("group_id".to_string(), "iot_consumer_group".to_string()),
            ("auto_offset_reset".to_string(), "earliest".to_string()),
        ]),
    };

    let manager = AdvancedProtocolManager::new(config);
    
    println!("  连接到Kafka集群...");
    manager.connect().await?;
    
    // 发送消息到Kafka主题
    let kafka_message = Message {
        id: uuid::Uuid::new_v4().to_string(),
        message_type: MessageType::Json(serde_json::json!({
            "device_id": "device_001",
            "event_type": "sensor_reading",
            "data": {
                "temperature": 25.5,
                "humidity": 60.0,
                "pressure": 1013.25
            },
            "timestamp": chrono::Utc::now()
        })),
        timestamp: chrono::Utc::now(),
        sender: "kafka_producer".to_string(),
        receiver: None,
        topic: Some("iot-events".to_string()),
        headers: HashMap::new(),
        payload: None,
    };
    
    println!("  发送消息到Kafka主题...");
    manager.send_message(kafka_message).await?;
    
    // 从Kafka主题消费消息
    println!("  从Kafka主题消费消息...");
    let consumed_message = manager.receive_message().await?;
    println!("  消费到消息: {:?}", consumed_message.message_type);
    
    manager.disconnect().await?;
    println!("  Kafka连接已断开");
    
    Ok(())
}

/// NATS协议演示
async fn demo_nats_protocol() -> Result<(), Box<dyn std::error::Error>> {
    let config = AdvancedProtocolConfig {
        protocol_type: AdvancedProtocolType::NATS,
        server_url: "nats://localhost:4222".to_string(),
        port: 4222,
        connection_timeout: Duration::from_secs(10),
        read_timeout: Duration::from_secs(30),
        write_timeout: Duration::from_secs(30),
        reconnect_interval: Duration::from_secs(5),
        max_reconnect_attempts: 3,
        enable_ssl: false,
        auth_info: None,
        custom_config: HashMap::new(),
    };

    let manager = AdvancedProtocolManager::new(config);
    
    println!("  连接到NATS服务器...");
    manager.connect().await?;
    
    // 发送NATS消息
    let nats_message = Message {
        id: uuid::Uuid::new_v4().to_string(),
        message_type: MessageType::Text("NATS轻量级消息".to_string()),
        timestamp: chrono::Utc::now(),
        sender: "nats_client".to_string(),
        receiver: None,
        topic: Some("iot.commands".to_string()),
        headers: HashMap::new(),
        payload: None,
    };
    
    println!("  发送NATS消息...");
    manager.send_message(nats_message).await?;
    
    // 接收NATS消息
    println!("  接收NATS消息...");
    let received_message = manager.receive_message().await?;
    println!("  收到消息: {:?}", received_message.message_type);
    
    manager.disconnect().await?;
    println!("  NATS连接已断开");
    
    Ok(())
}

/// 协议性能对比
async fn compare_protocol_performance() -> Result<(), Box<dyn std::error::Error>> {
    println!("  开始协议性能对比测试...");
    
    let protocols = vec![
        AdvancedProtocolType::WebSocket,
        AdvancedProtocolType::GRPC,
        AdvancedProtocolType::GraphQL,
        AdvancedProtocolType::AMQP,
        AdvancedProtocolType::Kafka,
        AdvancedProtocolType::NATS,
    ];
    
    let mut results = Vec::new();
    
    for protocol in protocols {
        println!("    测试 {:?} 协议...", protocol);
        
        let config = AdvancedProtocolConfig {
            protocol_type: protocol.clone(),
            server_url: format!("{}://localhost:8080", match protocol {
                AdvancedProtocolType::WebSocket => "ws",
                AdvancedProtocolType::GRPC => "grpc",
                AdvancedProtocolType::GraphQL => "http",
                AdvancedProtocolType::AMQP => "amqp",
                AdvancedProtocolType::Kafka => "kafka",
                AdvancedProtocolType::NATS => "nats",
                _ => "http",
            }),
            port: 8080,
            connection_timeout: Duration::from_secs(5),
            read_timeout: Duration::from_secs(10),
            write_timeout: Duration::from_secs(10),
            reconnect_interval: Duration::from_secs(2),
            max_reconnect_attempts: 2,
            enable_ssl: false,
            auth_info: None,
            custom_config: HashMap::new(),
        };
        
        let manager = AdvancedProtocolManager::new(config);
        
        // 测试连接时间
        let start = std::time::Instant::now();
        let connect_result = manager.connect().await;
        let connect_time = start.elapsed();
        
        if connect_result.is_ok() {
            // 测试消息发送时间
            let message = Message {
                id: uuid::Uuid::new_v4().to_string(),
                message_type: MessageType::Text("性能测试消息".to_string()),
                timestamp: chrono::Utc::now(),
                sender: "perf_test".to_string(),
                receiver: None,
                topic: None,
                headers: HashMap::new(),
                payload: None,
            };
            
            let start = std::time::Instant::now();
            let send_result = manager.send_message(message).await;
            let send_time = start.elapsed();
            
            if send_result.is_ok() {
                results.push((protocol, connect_time, send_time, true));
            } else {
                results.push((protocol, connect_time, Duration::ZERO, false));
            }
            
            let _ = manager.disconnect().await;
        } else {
            results.push((protocol, connect_time, Duration::ZERO, false));
        }
    }
    
    // 显示性能对比结果
    println!("  协议性能对比结果:");
    println!("    {:<15} {:<15} {:<15} {:<10}", "协议", "连接时间", "发送时间", "状态");
    println!("    {}", "-".repeat(60));
    
    for (protocol, connect_time, send_time, success) in results {
        let status = if success { "成功" } else { "失败" };
        println!("    {:<15} {:<15?} {:<15?} {:<10}", 
            format!("{:?}", protocol), 
            connect_time, 
            send_time, 
            status
        );
    }
    
    Ok(())
}
