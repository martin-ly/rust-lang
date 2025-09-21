//! 数字孪生集成演示示例
//! 
//! 展示如何使用c17_iot的数字孪生功能进行设备虚拟化、实时同步和预测性维护
#[allow(unused_imports)]
use c17_iot::digital_twin_integration::{
    DigitalTwinManager, 
    DigitalTwinConfig, 
    DigitalTwinModel, 
    RealtimeSyncConfig,
    PredictiveMaintenanceConfig, 
    DigitalTwinEvent, 
    DigitalTwinType, 
    DigitalTwinStatus,
    TwinProperty, 
    PropertyType, 
    PropertyValue, 
    TwinRelationship, 
    RelationshipType,
    TwinBehavior, 
    BehaviorType,
    BehaviorStatus, 
    SyncMode, 
    ConflictResolutionStrategy,
    MaintenanceType, 
    PredictionModel, 
    TwinEventType, 
    EventSeverity,
    DigitalTwinStats,
    DigitalTwinError,
    ConfigStatus,
};
use std::time::Duration;
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动数字孪生集成演示...");

    println!("📊 开始演示IoT系统数字孪生功能...");

    // 1. 数字孪生管理器创建和配置
    println!("\n1️⃣ 数字孪生管理器创建和配置");
    demo_digital_twin_manager_creation().await?;

    // 2. 数字孪生模型创建
    println!("\n2️⃣ 数字孪生模型创建");
    demo_digital_twin_creation().await?;

    // 3. 实时同步配置
    println!("\n3️⃣ 实时同步配置");
    demo_realtime_sync_configuration().await?;

    // 4. 预测性维护配置
    println!("\n4️⃣ 预测性维护配置");
    demo_predictive_maintenance_configuration().await?;

    // 5. 孪生属性管理
    println!("\n5️⃣ 孪生属性管理");
    demo_twin_property_management().await?;

    // 6. 孪生关系管理
    println!("\n6️⃣ 孪生关系管理");
    demo_twin_relationship_management().await?;

    // 7. 孪生行为管理
    println!("\n7️⃣ 孪生行为管理");
    demo_twin_behavior_management().await?;

    // 8. 实时同步演示
    println!("\n8️⃣ 实时同步演示");
    demo_realtime_sync().await?;

    // 9. 数字孪生统计和监控
    println!("\n9️⃣ 数字孪生统计和监控");
    demo_digital_twin_statistics().await?;

    println!("\n✅ 数字孪生集成演示完成!");
    println!("🎯 演示展示了以下功能:");
    println!("  - 数字孪生模型创建");
    println!("  - 实时同步配置");
    println!("  - 预测性维护配置");
    println!("  - 孪生属性和关系管理");
    println!("  - 孪生行为管理");

    Ok(())
}

/// 数字孪生管理器创建和配置演示
async fn demo_digital_twin_manager_creation() -> Result<(), Box<dyn std::error::Error>> {
    // 创建数字孪生配置
    let config = DigitalTwinConfig {
        enable_digital_twin: true,
        enable_realtime_sync: true,
        enable_predictive_maintenance: true,
        default_sync_interval: Duration::from_secs(60),
        max_twin_count: 1000,
        event_retention_time: Duration::from_secs(86400 * 30), // 30天
        custom_params: HashMap::new(),
    };

    println!("  创建数字孪生管理器...");
    let twin_manager = DigitalTwinManager::new(config);
    
    // 获取初始统计信息
    let stats = twin_manager.get_stats().await;
    println!("  初始数字孪生统计:");
    println!("    总孪生数量: {}", stats.total_twins);
    println!("    活跃孪生数量: {}", stats.active_twins);
    println!("    同步中孪生数量: {}", stats.syncing_twins);
    println!("    错误孪生数量: {}", stats.error_twins);
    println!("    总事件数量: {}", stats.total_events);
    println!("    预测性维护配置数量: {}", stats.maintenance_configs_count);
    println!("    实时同步配置数量: {}", stats.sync_configs_count);

    Ok(())
}

/// 数字孪生模型创建演示
async fn demo_digital_twin_creation() -> Result<(), Box<dyn std::error::Error>> {
    let twin_manager = DigitalTwinManager::new(DigitalTwinConfig::default());
    
    println!("  创建数字孪生模型...");
    
    // 创建设备孪生
    let device_twin = create_digital_twin_model(
        "device_twin_001",
        "智能传感器设备孪生",
        DigitalTwinType::DeviceTwin,
        "sensor_device_001",
        create_device_properties(),
    );
    
    let device_twin_id = twin_manager.create_digital_twin(device_twin).await?;
    println!("    设备孪生已创建: {}", device_twin_id);
    
    // 创建系统孪生
    let system_twin = create_digital_twin_model(
        "system_twin_001",
        "IoT系统孪生",
        DigitalTwinType::SystemTwin,
        "iot_system_001",
        create_system_properties(),
    );
    
    let system_twin_id = twin_manager.create_digital_twin(system_twin).await?;
    println!("    系统孪生已创建: {}", system_twin_id);
    
    // 创建过程孪生
    let process_twin = create_digital_twin_model(
        "process_twin_001",
        "制造过程孪生",
        DigitalTwinType::ProcessTwin,
        "manufacturing_process_001",
        create_process_properties(),
    );
    
    let process_twin_id = twin_manager.create_digital_twin(process_twin).await?;
    println!("    过程孪生已创建: {}", process_twin_id);
    
    // 创建产品孪生
    let product_twin = create_digital_twin_model(
        "product_twin_001",
        "智能产品孪生",
        DigitalTwinType::ProductTwin,
        "smart_product_001",
        create_product_properties(),
    );
    
    let product_twin_id = twin_manager.create_digital_twin(product_twin).await?;
    println!("    产品孪生已创建: {}", product_twin_id);
    
    // 创建环境孪生
    let environment_twin = create_digital_twin_model(
        "environment_twin_001",
        "环境监测孪生",
        DigitalTwinType::EnvironmentTwin,
        "environment_monitor_001",
        create_environment_properties(),
    );
    
    let environment_twin_id = twin_manager.create_digital_twin(environment_twin).await?;
    println!("    环境孪生已创建: {}", environment_twin_id);
    
    // 获取数字孪生列表
    let all_twins = twin_manager.get_digital_twins(None, None).await;
    println!("  数字孪生统计:");
    println!("    总孪生数量: {}", all_twins.len());
    
    let mut twin_type_count = HashMap::new();
    for twin in &all_twins {
        *twin_type_count.entry(&twin.twin_type).or_insert(0) += 1;
    }
    
    for (twin_type, count) in twin_type_count {
        println!("    {:?}: {} 个", twin_type, count);
    }
    
    // 显示孪生详情
    for twin in &all_twins {
        println!("    孪生: {} - {:?} - 属性数: {}", 
                twin.model_name, 
                twin.twin_type, 
                twin.properties.len());
        println!("      物理实体ID: {}", twin.physical_entity_id);
        println!("      状态: {:?}", twin.status);
        println!("      版本: {}", twin.model_version);
    }

    Ok(())
}

/// 实时同步配置演示
async fn demo_realtime_sync_configuration() -> Result<(), Box<dyn std::error::Error>> {
    let twin_manager = DigitalTwinManager::new(DigitalTwinConfig::default());
    
    println!("  创建实时同步配置...");
    
    // 创建实时同步配置
    let realtime_sync_config = RealtimeSyncConfig {
        config_id: "realtime_sync_001".to_string(),
        sync_interval: Duration::from_secs(30),
        sync_mode: SyncMode::Realtime,
        sync_properties: vec![
            "temperature".to_string(),
            "pressure".to_string(),
            "humidity".to_string(),
            "status".to_string(),
        ],
        data_compression: true,
        incremental_sync: true,
        conflict_resolution: ConflictResolutionStrategy::PhysicalEntityWins,
        status: c17_iot::digital_twin_integration::ConfigStatus::Active,
    };
    
    let realtime_config_id = twin_manager.create_sync_config(realtime_sync_config).await?;
    println!("    实时同步配置已创建: {}", realtime_config_id);
    
    // 创建定时同步配置
    let scheduled_sync_config = RealtimeSyncConfig {
        config_id: "scheduled_sync_001".to_string(),
        sync_interval: Duration::from_secs(300), // 5分钟
        sync_mode: SyncMode::Scheduled,
        sync_properties: vec![
            "configuration".to_string(),
            "maintenance_status".to_string(),
        ],
        data_compression: false,
        incremental_sync: false,
        conflict_resolution: ConflictResolutionStrategy::TimestampWins,
        status: c17_iot::digital_twin_integration::ConfigStatus::Active,
    };
    
    let scheduled_config_id = twin_manager.create_sync_config(scheduled_sync_config).await?;
    println!("    定时同步配置已创建: {}", scheduled_config_id);
    
    // 创建事件驱动同步配置
    let event_driven_sync_config = RealtimeSyncConfig {
        config_id: "event_driven_sync_001".to_string(),
        sync_interval: Duration::from_secs(1),
        sync_mode: SyncMode::EventDriven,
        sync_properties: vec![
            "alarm_status".to_string(),
            "error_codes".to_string(),
        ],
        data_compression: true,
        incremental_sync: true,
        conflict_resolution: ConflictResolutionStrategy::DigitalTwinWins,
        status: c17_iot::digital_twin_integration::ConfigStatus::Active,
    };
    
    let event_driven_config_id = twin_manager.create_sync_config(event_driven_sync_config).await?;
    println!("    事件驱动同步配置已创建: {}", event_driven_config_id);

    Ok(())
}

/// 预测性维护配置演示
async fn demo_predictive_maintenance_configuration() -> Result<(), Box<dyn std::error::Error>> {
    let twin_manager = DigitalTwinManager::new(DigitalTwinConfig::default());
    
    println!("  创建预测性维护配置...");
    
    // 创建预测性维护配置
    let predictive_maintenance_config = PredictiveMaintenanceConfig {
        config_id: "predictive_maintenance_001".to_string(),
        maintenance_type: MaintenanceType::Predictive,
        prediction_model: PredictionModel::MachineLearning,
        warning_thresholds: HashMap::from([
            ("temperature".to_string(), 80.0),
            ("vibration".to_string(), 5.0),
            ("pressure".to_string(), 100.0),
        ]),
        maintenance_interval: Duration::from_secs(86400 * 7), // 7天
        maintenance_duration: Duration::from_secs(3600), // 1小时
        status: c17_iot::digital_twin_integration::ConfigStatus::Active,
    };
    
    let predictive_config_id = twin_manager.create_maintenance_config(predictive_maintenance_config).await?;
    println!("    预测性维护配置已创建: {}", predictive_config_id);
    
    // 创建条件性维护配置
    let condition_based_maintenance_config = PredictiveMaintenanceConfig {
        config_id: "condition_based_maintenance_001".to_string(),
        maintenance_type: MaintenanceType::ConditionBased,
        prediction_model: PredictionModel::Statistical,
        warning_thresholds: HashMap::from([
            ("current".to_string(), 10.0),
            ("voltage".to_string(), 240.0),
            ("power".to_string(), 2000.0),
        ]),
        maintenance_interval: Duration::from_secs(86400 * 30), // 30天
        maintenance_duration: Duration::from_secs(7200), // 2小时
        status: c17_iot::digital_twin_integration::ConfigStatus::Active,
    };
    
    let condition_based_config_id = twin_manager.create_maintenance_config(condition_based_maintenance_config).await?;
    println!("    条件性维护配置已创建: {}", condition_based_config_id);
    
    // 创建预防性维护配置
    let preventive_maintenance_config = PredictiveMaintenanceConfig {
        config_id: "preventive_maintenance_001".to_string(),
        maintenance_type: MaintenanceType::Preventive,
        prediction_model: PredictionModel::PhysicsBased,
        warning_thresholds: HashMap::from([
            ("operating_hours".to_string(), 8000.0),
            ("cycle_count".to_string(), 10000.0),
        ]),
        maintenance_interval: Duration::from_secs(86400 * 90), // 90天
        maintenance_duration: Duration::from_secs(14400), // 4小时
        status: c17_iot::digital_twin_integration::ConfigStatus::Active,
    };
    
    let preventive_config_id = twin_manager.create_maintenance_config(preventive_maintenance_config).await?;
    println!("    预防性维护配置已创建: {}", preventive_config_id);

    Ok(())
}

/// 孪生属性管理演示
async fn demo_twin_property_management() -> Result<(), Box<dyn std::error::Error>> {
    let twin_manager = DigitalTwinManager::new(DigitalTwinConfig::default());
    
    println!("  孪生属性管理演示...");
    
    // 创建设备孪生
    let device_twin = create_digital_twin_model(
        "property_test_twin",
        "属性测试孪生",
        DigitalTwinType::DeviceTwin,
        "test_device_001",
        create_device_properties(),
    );
    
    let twin_id = twin_manager.create_digital_twin(device_twin).await?;
    println!("    测试孪生已创建: {}", twin_id);
    
    // 更新温度属性
    twin_manager.update_twin_property(
        &twin_id,
        "temperature",
        PropertyValue::Float(25.5),
    ).await?;
    println!("    温度属性已更新: 25.5°C");
    
    // 更新压力属性
    twin_manager.update_twin_property(
        &twin_id,
        "pressure",
        PropertyValue::Float(1013.25),
    ).await?;
    println!("    压力属性已更新: 1013.25 hPa");
    
    // 更新湿度属性
    twin_manager.update_twin_property(
        &twin_id,
        "humidity",
        PropertyValue::Float(60.0),
    ).await?;
    println!("    湿度属性已更新: 60.0%");
    
    // 更新状态属性
    twin_manager.update_twin_property(
        &twin_id,
        "status",
        PropertyValue::String("running".to_string()),
    ).await?;
    println!("    状态属性已更新: running");
    
    // 更新配置属性
    let mut config_data = HashMap::new();
    config_data.insert("sampling_rate".to_string(), PropertyValue::Integer(1000));
    config_data.insert("resolution".to_string(), PropertyValue::String("16bit".to_string()));
    config_data.insert("calibration_date".to_string(), PropertyValue::String("2025-01-01".to_string()));
    
    twin_manager.update_twin_property(
        &twin_id,
        "configuration",
        PropertyValue::Object(config_data),
    ).await?;
    println!("    配置属性已更新: 包含采样率、分辨率和校准日期");
    
    // 获取更新后的孪生信息
    let updated_twin = twin_manager.get_digital_twin(&twin_id).await?;
    println!("  更新后的孪生属性:");
    for (name, property) in &updated_twin.properties {
        println!("    {}: {:?} ({:?})", name, property.value, property.property_type);
        if let Some(unit) = &property.unit {
            println!("      单位: {}", unit);
        }
        println!("      可写: {}, 更新时间: {}", 
                property.writable, 
                property.updated_at.format("%H:%M:%S"));
    }

    Ok(())
}

/// 孪生关系管理演示
async fn demo_twin_relationship_management() -> Result<(), Box<dyn std::error::Error>> {
    let twin_manager = DigitalTwinManager::new(DigitalTwinConfig::default());
    
    println!("  孪生关系管理演示...");
    
    // 创建多个孪生
    let system_twin = create_digital_twin_model(
        "system_twin_002",
        "系统孪生",
        DigitalTwinType::SystemTwin,
        "system_002",
        create_system_properties(),
    );
    
    let device_twin1 = create_digital_twin_model(
        "device_twin_002",
        "设备孪生1",
        DigitalTwinType::DeviceTwin,
        "device_002",
        create_device_properties(),
    );
    
    let device_twin2 = create_digital_twin_model(
        "device_twin_003",
        "设备孪生2",
        DigitalTwinType::DeviceTwin,
        "device_003",
        create_device_properties(),
    );
    
    let system_id = twin_manager.create_digital_twin(system_twin).await?;
    let device_id1 = twin_manager.create_digital_twin(device_twin1).await?;
    let device_id2 = twin_manager.create_digital_twin(device_twin2).await?;
    
    println!("    系统孪生已创建: {}", system_id);
    println!("    设备孪生1已创建: {}", device_id1);
    println!("    设备孪生2已创建: {}", device_id2);
    
    // 获取孪生信息以查看关系
    let system_twin_info = twin_manager.get_digital_twin(&system_id).await?;
    let device_twin1_info = twin_manager.get_digital_twin(&device_id1).await?;
    let device_twin2_info = twin_manager.get_digital_twin(&device_id2).await?;
    
    println!("  孪生关系信息:");
    println!("    系统孪生关系数: {}", system_twin_info.relationships.len());
    println!("    设备孪生1关系数: {}", device_twin1_info.relationships.len());
    println!("    设备孪生2关系数: {}", device_twin2_info.relationships.len());
    
    // 显示关系详情
    for (i, relationship) in system_twin_info.relationships.iter().enumerate() {
        println!("    关系 {}: {} ({:?})", 
                i + 1, 
                relationship.relationship_name, 
                relationship.relationship_type);
        println!("      源孪生: {}", relationship.source_twin_id);
        println!("      目标孪生: {}", relationship.target_twin_id);
        println!("      属性数: {}", relationship.properties.len());
    }

    Ok(())
}

/// 孪生行为管理演示
async fn demo_twin_behavior_management() -> Result<(), Box<dyn std::error::Error>> {
    let twin_manager = DigitalTwinManager::new(DigitalTwinConfig::default());
    
    println!("  孪生行为管理演示...");
    
    // 创建带有行为的孪生
    let device_properties = create_device_properties();
    let mut behaviors = Vec::new();
    
    // 添加数据同步行为
    behaviors.push(TwinBehavior {
        behavior_id: "data_sync_behavior".to_string(),
        behavior_name: "数据同步行为".to_string(),
        behavior_type: BehaviorType::DataSync,
        description: "定期同步设备数据到云端".to_string(),
        parameters: HashMap::from([
            ("sync_interval".to_string(), PropertyValue::Integer(60)),
            ("data_format".to_string(), PropertyValue::String("json".to_string())),
        ]),
        status: BehaviorStatus::Running,
        execution_time: Some(Duration::from_secs(5)),
        last_execution: Some(chrono::Utc::now()),
    });
    
    // 添加异常检测行为
    behaviors.push(TwinBehavior {
        behavior_id: "anomaly_detection_behavior".to_string(),
        behavior_name: "异常检测行为".to_string(),
        behavior_type: BehaviorType::AnomalyDetection,
        description: "检测设备运行异常".to_string(),
        parameters: HashMap::from([
            ("threshold".to_string(), PropertyValue::Float(3.0)),
            ("window_size".to_string(), PropertyValue::Integer(100)),
        ]),
        status: BehaviorStatus::Running,
        execution_time: Some(Duration::from_secs(2)),
        last_execution: Some(chrono::Utc::now()),
    });
    
    // 添加预测分析行为
    behaviors.push(TwinBehavior {
        behavior_id: "predictive_analysis_behavior".to_string(),
        behavior_name: "预测分析行为".to_string(),
        behavior_type: BehaviorType::PredictiveAnalysis,
        description: "预测设备维护需求".to_string(),
        parameters: HashMap::from([
            ("prediction_horizon".to_string(), PropertyValue::Integer(30)),
            ("confidence_level".to_string(), PropertyValue::Float(0.95)),
        ]),
        status: BehaviorStatus::Pending,
        execution_time: None,
        last_execution: None,
    });
    
    let device_twin = DigitalTwinModel {
        model_id: "behavior_test_twin".to_string(),
        model_name: "行为测试孪生".to_string(),
        twin_type: DigitalTwinType::DeviceTwin,
        physical_entity_id: "behavior_test_device".to_string(),
        model_version: "1.0.0".to_string(),
        status: DigitalTwinStatus::Active,
        properties: device_properties,
        relationships: Vec::new(),
        behaviors,
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
        last_sync_time: None,
    };
    
    let twin_id = twin_manager.create_digital_twin(device_twin).await?;
    println!("    行为测试孪生已创建: {}", twin_id);
    
    // 获取孪生信息以查看行为
    let twin_info = twin_manager.get_digital_twin(&twin_id).await?;
    println!("  孪生行为信息:");
    println!("    总行为数: {}", twin_info.behaviors.len());
    
    for (i, behavior) in twin_info.behaviors.iter().enumerate() {
        println!("    行为 {}: {} ({:?})", 
                i + 1, 
                behavior.behavior_name, 
                behavior.behavior_type);
        println!("      描述: {}", behavior.description);
        println!("      状态: {:?}", behavior.status);
        println!("      参数数: {}", behavior.parameters.len());
        if let Some(execution_time) = behavior.execution_time {
            println!("      执行时间: {:?}", execution_time);
        }
        if let Some(last_execution) = behavior.last_execution {
            println!("      最后执行: {}", last_execution.format("%H:%M:%S"));
        }
    }

    Ok(())
}

/// 实时同步演示
async fn demo_realtime_sync() -> Result<(), Box<dyn std::error::Error>> {
    let twin_manager = DigitalTwinManager::new(DigitalTwinConfig::default());
    
    println!("  启动实时同步演示...");
    
    // 创建一些测试孪生
    for i in 1..=3 {
        let device_twin = create_digital_twin_model(
            &format!("sync_test_twin_{}", i),
            &format!("同步测试孪生 {}", i),
            DigitalTwinType::DeviceTwin,
            &format!("sync_test_device_{}", i),
            create_device_properties(),
        );
        
        let twin_id = twin_manager.create_digital_twin(device_twin).await?;
        println!("    同步测试孪生已创建: {}", twin_id);
    }
    
    // 启动实时同步
    let twin_manager_arc = std::sync::Arc::new(twin_manager);
    twin_manager_arc.clone().start_realtime_sync().await;
    
    println!("    实时同步引擎已启动");
    
    // 等待同步运行
    println!("    等待实时同步运行...");
    tokio::time::sleep(Duration::from_secs(3)).await;
    
    // 检查同步事件
    let sync_events = twin_manager_arc.get_twin_events(None, Some(10)).await;
    println!("  同步事件统计:");
    println!("    总事件数: {}", sync_events.len());
    
    let mut event_type_count = HashMap::new();
    for event in &sync_events {
        *event_type_count.entry(&event.event_type).or_insert(0) += 1;
    }
    
    for (event_type, count) in event_type_count {
        println!("    {:?}: {} 个", event_type, count);
    }
    
    // 显示最近的同步事件
    for (i, event) in sync_events.iter().enumerate() {
        if i >= 5 { break; } // 只显示前5个事件
        println!("    事件 {}: {:?} - {:?} - {}", 
                i + 1, 
                event.event_type, 
                event.severity, 
                event.description);
        println!("      孪生ID: {}, 时间: {}", 
                event.twin_id, 
                event.timestamp.format("%H:%M:%S"));
    }

    Ok(())
}

/// 数字孪生统计和监控演示
async fn demo_digital_twin_statistics() -> Result<(), Box<dyn std::error::Error>> {
    let twin_manager = DigitalTwinManager::new(DigitalTwinConfig::default());
    
    println!("  生成数字孪生统计报告...");
    
    // 执行一些操作以生成统计数据
    // 创建一些数字孪生
    for i in 1..=5 {
        let device_twin = create_digital_twin_model(
            &format!("stats_twin_{}", i),
            &format!("统计测试孪生 {}", i),
            DigitalTwinType::DeviceTwin,
            &format!("stats_device_{}", i),
            create_device_properties(),
        );
        twin_manager.create_digital_twin(device_twin).await?;
    }
    
    // 创建一些同步配置
    for i in 1..=3 {
        let sync_config = RealtimeSyncConfig {
            config_id: format!("stats_sync_config_{}", i),
            sync_interval: Duration::from_secs(60),
            sync_mode: SyncMode::Realtime,
            sync_properties: vec!["temperature".to_string(), "pressure".to_string()],
            data_compression: true,
            incremental_sync: true,
            conflict_resolution: ConflictResolutionStrategy::PhysicalEntityWins,
            status: c17_iot::digital_twin_integration::ConfigStatus::Active,
        };
        twin_manager.create_sync_config(sync_config).await?;
    }
    
    // 创建一些维护配置
    for i in 1..=2 {
        let maintenance_config = PredictiveMaintenanceConfig {
            config_id: format!("stats_maintenance_config_{}", i),
            maintenance_type: MaintenanceType::Predictive,
            prediction_model: PredictionModel::MachineLearning,
            warning_thresholds: HashMap::from([
                ("temperature".to_string(), 80.0),
                ("vibration".to_string(), 5.0),
            ]),
            maintenance_interval: Duration::from_secs(86400 * 7),
            maintenance_duration: Duration::from_secs(3600),
            status: c17_iot::digital_twin_integration::ConfigStatus::Active,
        };
        twin_manager.create_maintenance_config(maintenance_config).await?;
    }
    
    // 获取统计信息
    let stats = twin_manager.get_stats().await;
    println!("  数字孪生统计报告:");
    println!("    总孪生数量: {}", stats.total_twins);
    println!("    活跃孪生数量: {}", stats.active_twins);
    println!("    同步中孪生数量: {}", stats.syncing_twins);
    println!("    错误孪生数量: {}", stats.error_twins);
    println!("    总事件数量: {}", stats.total_events);
    println!("    预测性维护配置数量: {}", stats.maintenance_configs_count);
    println!("    实时同步配置数量: {}", stats.sync_configs_count);
    println!("    最后更新时间: {}", stats.last_updated.format("%Y-%m-%d %H:%M:%S"));
    
    // 获取数字孪生列表
    let all_twins = twin_manager.get_digital_twins(None, Some(10)).await;
    println!("  最近数字孪生 ({} 个):", all_twins.len());
    for (i, twin) in all_twins.iter().enumerate() {
        println!("    {}: {} ({:?}) - {:?}", 
                i + 1, 
                twin.model_name, 
                twin.twin_type, 
                twin.status);
        println!("      物理实体ID: {}", twin.physical_entity_id);
        println!("      属性数: {}, 关系数: {}, 行为数: {}", 
                twin.properties.len(), 
                twin.relationships.len(), 
                twin.behaviors.len());
    }
    
    // 获取孪生事件列表
    let all_events = twin_manager.get_twin_events(None, Some(10)).await;
    println!("  最近孪生事件 ({} 个):", all_events.len());
    for (i, event) in all_events.iter().enumerate() {
        println!("    {}: {:?} - {:?} - {}", 
                i + 1, 
                event.event_type, 
                event.severity, 
                event.description);
        println!("      孪生ID: {}, 时间: {}", 
                event.twin_id, 
                event.timestamp.format("%H:%M:%S"));
    }

    Ok(())
}

/// 创建数字孪生模型的辅助函数
fn create_digital_twin_model(
    model_id: &str,
    model_name: &str,
    twin_type: DigitalTwinType,
    physical_entity_id: &str,
    properties: HashMap<String, TwinProperty>,
) -> DigitalTwinModel {
    DigitalTwinModel {
        model_id: model_id.to_string(),
        model_name: model_name.to_string(),
        twin_type,
        physical_entity_id: physical_entity_id.to_string(),
        model_version: "1.0.0".to_string(),
        status: DigitalTwinStatus::Active,
        properties,
        relationships: Vec::new(),
        behaviors: Vec::new(),
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
        last_sync_time: None,
    }
}

/// 创建设备属性的辅助函数
fn create_device_properties() -> HashMap<String, TwinProperty> {
    let mut properties = HashMap::new();
    
    properties.insert("temperature".to_string(), TwinProperty {
        name: "temperature".to_string(),
        property_type: PropertyType::Temperature,
        value: PropertyValue::Float(25.0),
        unit: Some("°C".to_string()),
        description: Some("设备温度".to_string()),
        writable: false,
        updated_at: chrono::Utc::now(),
    });
    
    properties.insert("pressure".to_string(), TwinProperty {
        name: "pressure".to_string(),
        property_type: PropertyType::Pressure,
        value: PropertyValue::Float(1013.25),
        unit: Some("hPa".to_string()),
        description: Some("环境压力".to_string()),
        writable: false,
        updated_at: chrono::Utc::now(),
    });
    
    properties.insert("humidity".to_string(), TwinProperty {
        name: "humidity".to_string(),
        property_type: PropertyType::Humidity,
        value: PropertyValue::Float(50.0),
        unit: Some("%".to_string()),
        description: Some("相对湿度".to_string()),
        writable: false,
        updated_at: chrono::Utc::now(),
    });
    
    properties.insert("status".to_string(), TwinProperty {
        name: "status".to_string(),
        property_type: PropertyType::Status,
        value: PropertyValue::String("online".to_string()),
        unit: None,
        description: Some("设备状态".to_string()),
        writable: true,
        updated_at: chrono::Utc::now(),
    });
    
    properties
}

/// 创建系统属性的辅助函数
fn create_system_properties() -> HashMap<String, TwinProperty> {
    let mut properties = HashMap::new();
    
    properties.insert("system_load".to_string(), TwinProperty {
        name: "system_load".to_string(),
        property_type: PropertyType::Custom("system_load".to_string()),
        value: PropertyValue::Float(0.75),
        unit: Some("%".to_string()),
        description: Some("系统负载".to_string()),
        writable: false,
        updated_at: chrono::Utc::now(),
    });
    
    properties.insert("connected_devices".to_string(), TwinProperty {
        name: "connected_devices".to_string(),
        property_type: PropertyType::Custom("device_count".to_string()),
        value: PropertyValue::Integer(10),
        unit: Some("个".to_string()),
        description: Some("连接的设备数量".to_string()),
        writable: false,
        updated_at: chrono::Utc::now(),
    });
    
    properties
}

/// 创建过程属性的辅助函数
fn create_process_properties() -> HashMap<String, TwinProperty> {
    let mut properties = HashMap::new();
    
    properties.insert("production_rate".to_string(), TwinProperty {
        name: "production_rate".to_string(),
        property_type: PropertyType::Custom("production_rate".to_string()),
        value: PropertyValue::Float(100.0),
        unit: Some("件/小时".to_string()),
        description: Some("生产效率".to_string()),
        writable: true,
        updated_at: chrono::Utc::now(),
    });
    
    properties.insert("quality_rate".to_string(), TwinProperty {
        name: "quality_rate".to_string(),
        property_type: PropertyType::Custom("quality_rate".to_string()),
        value: PropertyValue::Float(98.5),
        unit: Some("%".to_string()),
        description: Some("质量合格率".to_string()),
        writable: false,
        updated_at: chrono::Utc::now(),
    });
    
    properties
}

/// 创建产品属性的辅助函数
fn create_product_properties() -> HashMap<String, TwinProperty> {
    let mut properties = HashMap::new();
    
    properties.insert("product_id".to_string(), TwinProperty {
        name: "product_id".to_string(),
        property_type: PropertyType::Custom("product_id".to_string()),
        value: PropertyValue::String("PROD_001".to_string()),
        unit: None,
        description: Some("产品ID".to_string()),
        writable: false,
        updated_at: chrono::Utc::now(),
    });
    
    properties.insert("serial_number".to_string(), TwinProperty {
        name: "serial_number".to_string(),
        property_type: PropertyType::Custom("serial_number".to_string()),
        value: PropertyValue::String("SN123456789".to_string()),
        unit: None,
        description: Some("序列号".to_string()),
        writable: false,
        updated_at: chrono::Utc::now(),
    });
    
    properties
}

/// 创建环境属性的辅助函数
fn create_environment_properties() -> HashMap<String, TwinProperty> {
    let mut properties = HashMap::new();
    
    properties.insert("air_quality".to_string(), TwinProperty {
        name: "air_quality".to_string(),
        property_type: PropertyType::Custom("air_quality".to_string()),
        value: PropertyValue::String("good".to_string()),
        unit: None,
        description: Some("空气质量".to_string()),
        writable: false,
        updated_at: chrono::Utc::now(),
    });
    
    properties.insert("noise_level".to_string(), TwinProperty {
        name: "noise_level".to_string(),
        property_type: PropertyType::Custom("noise_level".to_string()),
        value: PropertyValue::Float(45.0),
        unit: Some("dB".to_string()),
        description: Some("噪音水平".to_string()),
        writable: false,
        updated_at: chrono::Utc::now(),
    });
    
    properties
}
