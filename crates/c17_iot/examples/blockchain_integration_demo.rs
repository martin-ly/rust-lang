//! 区块链集成演示示例
//! 
//! 展示如何使用c17_iot的区块链集成功能进行智能合约、数字身份和供应链溯源

use c17_iot::blockchain_integration::{
    BlockchainIntegrationManager, BlockchainConfig, BlockchainType, SmartContractConfig,
    IdentityType, OperationType, Location, SupplyChainRecord
};
use std::time::Duration;
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动区块链集成演示...");

    println!("📊 开始演示IoT系统区块链集成功能...");

    // 1. 区块链集成管理器创建和配置
    println!("\n1️⃣ 区块链集成管理器创建和配置");
    demo_blockchain_manager_creation().await?;

    // 2. 智能合约部署和调用
    println!("\n2️⃣ 智能合约部署和调用");
    demo_smart_contract_operations().await?;

    // 3. 数字身份管理
    println!("\n3️⃣ 数字身份管理");
    demo_digital_identity_management().await?;

    // 4. 供应链溯源
    println!("\n4️⃣ 供应链溯源");
    demo_supply_chain_tracing().await?;

    // 5. 区块链交易
    println!("\n5️⃣ 区块链交易");
    demo_blockchain_transactions().await?;

    // 6. 多区块链网络支持
    println!("\n6️⃣ 多区块链网络支持");
    demo_multi_blockchain_support().await?;

    // 7. 数据存储和查询
    println!("\n7️⃣ 数据存储和查询");
    demo_data_storage_and_query().await?;

    // 8. 区块链统计和报告
    println!("\n8️⃣ 区块链统计和报告");
    demo_blockchain_statistics().await?;

    println!("\n✅ 区块链集成演示完成!");
    println!("🎯 演示展示了以下功能:");
    println!("  - 智能合约部署和调用");
    println!("  - 数字身份创建和验证");
    println!("  - 供应链溯源记录");
    println!("  - 区块链交易处理");
    println!("  - 多区块链网络支持");

    Ok(())
}

/// 区块链集成管理器创建和配置演示
async fn demo_blockchain_manager_creation() -> Result<(), Box<dyn std::error::Error>> {
    // 创建以太坊配置
    let ethereum_config = BlockchainConfig {
        blockchain_type: BlockchainType::Ethereum,
        network_url: "https://mainnet.infura.io/v3/your-project-id".to_string(),
        network_id: 1,
        enabled: true,
        connection_timeout: Duration::from_secs(30),
        retry_count: 3,
        retry_interval: Duration::from_secs(5),
        enable_encryption: true,
        private_key_path: Some("/path/to/private/key".to_string()),
        custom_params: HashMap::new(),
    };

    println!("  创建区块链集成管理器...");
    let blockchain_manager = BlockchainIntegrationManager::new(ethereum_config);
    
    // 获取初始统计信息
    let stats = blockchain_manager.get_stats().await;
    println!("  初始区块链统计:");
    println!("    总交易数: {}", stats.total_transactions);
    println!("    成功交易数: {}", stats.successful_transactions);
    println!("    失败交易数: {}", stats.failed_transactions);
    println!("    数字身份数量: {}", stats.digital_identity_count);
    println!("    供应链记录数量: {}", stats.supply_chain_record_count);

    Ok(())
}

/// 智能合约部署和调用演示
async fn demo_smart_contract_operations() -> Result<(), Box<dyn std::error::Error>> {
    let blockchain_manager = BlockchainIntegrationManager::new(BlockchainConfig {
        blockchain_type: BlockchainType::Ethereum,
        network_url: "https://mainnet.infura.io".to_string(),
        network_id: 1,
        enabled: true,
        connection_timeout: Duration::from_secs(30),
        retry_count: 3,
        retry_interval: Duration::from_secs(5),
        enable_encryption: true,
        private_key_path: None,
        custom_params: HashMap::new(),
    });
    
    println!("  部署智能合约...");
    
    // 部署IoT数据管理合约
    let iot_contract_config = SmartContractConfig {
        contract_address: "".to_string(),
        contract_abi: r#"[{"inputs":[],"name":"getData","outputs":[{"internalType":"string","name":"","type":"string"}],"stateMutability":"view","type":"function"}]"#.to_string(),
        contract_name: "IoTDataManager".to_string(),
        contract_version: "1.0".to_string(),
        network: "mainnet".to_string(),
        deployer_address: "0x1234567890123456789012345678901234567890".to_string(),
        gas_limit: 2000000,
        gas_price: 20000000000, // 20 Gwei
        custom_params: HashMap::new(),
    };
    
    let contract_address = blockchain_manager.deploy_smart_contract(iot_contract_config).await?;
    println!("    IoT数据管理合约已部署到: {}", contract_address);
    
    // 部署设备管理合约
    let device_contract_config = SmartContractConfig {
        contract_address: "".to_string(),
        contract_abi: r#"[{"inputs":[{"internalType":"string","name":"deviceId","type":"string"}],"name":"registerDevice","outputs":[],"stateMutability":"nonpayable","type":"function"}]"#.to_string(),
        contract_name: "DeviceManager".to_string(),
        contract_version: "1.0".to_string(),
        network: "mainnet".to_string(),
        deployer_address: "0x1234567890123456789012345678901234567890".to_string(),
        gas_limit: 1500000,
        gas_price: 20000000000,
        custom_params: HashMap::new(),
    };
    
    let device_contract_address = blockchain_manager.deploy_smart_contract(device_contract_config).await?;
    println!("    设备管理合约已部署到: {}", device_contract_address);
    
    println!("  调用智能合约...");
    
    // 调用IoT数据管理合约
    let data_result = blockchain_manager.call_smart_contract(
        &contract_address,
        "getData",
        vec!["sensor_data".to_string()]
    ).await?;
    println!("    获取数据结果: {}", data_result);
    
    // 调用设备管理合约
    let device_result = blockchain_manager.call_smart_contract(
        &device_contract_address,
        "registerDevice",
        vec!["device_001".to_string()]
    ).await?;
    println!("    设备注册结果: {}", device_result);
    
    // 获取已部署的智能合约列表
    let contracts = blockchain_manager.get_smart_contracts().await;
    println!("  已部署的智能合约数量: {}", contracts.len());
    for contract in contracts {
        println!("    - {}: {}", contract.contract_name, contract.contract_address);
    }

    Ok(())
}

/// 数字身份管理演示
async fn demo_digital_identity_management() -> Result<(), Box<dyn std::error::Error>> {
    let blockchain_manager = BlockchainIntegrationManager::new(BlockchainConfig {
        blockchain_type: BlockchainType::Ethereum,
        network_url: "https://mainnet.infura.io".to_string(),
        network_id: 1,
        enabled: true,
        connection_timeout: Duration::from_secs(30),
        retry_count: 3,
        retry_interval: Duration::from_secs(5),
        enable_encryption: true,
        private_key_path: None,
        custom_params: HashMap::new(),
    });
    
    println!("  创建数字身份...");
    
    // 创建设备身份
    let device_attributes = HashMap::from([
        ("device_type".to_string(), "temperature_sensor".to_string()),
        ("manufacturer".to_string(), "IoT Corp".to_string()),
        ("model".to_string(), "TS-2024".to_string()),
        ("serial_number".to_string(), "TS2024001".to_string()),
        ("location".to_string(), "Building A, Floor 1".to_string()),
    ]);
    
    let device_identity = blockchain_manager.create_digital_identity(IdentityType::Device, device_attributes).await?;
    println!("    设备身份已创建:");
    println!("      身份ID: {}", device_identity.identity_id);
    println!("      身份地址: {}", device_identity.identity_address);
    println!("      身份类型: {:?}", device_identity.identity_type);
    println!("      是否已验证: {}", device_identity.is_verified);
    
    // 创建用户身份
    let user_attributes = HashMap::from([
        ("name".to_string(), "张三".to_string()),
        ("email".to_string(), "zhangsan@example.com".to_string()),
        ("role".to_string(), "system_administrator".to_string()),
        ("department".to_string(), "IT".to_string()),
    ]);
    
    let user_identity = blockchain_manager.create_digital_identity(IdentityType::User, user_attributes).await?;
    println!("    用户身份已创建:");
    println!("      身份ID: {}", user_identity.identity_id);
    println!("      身份地址: {}", user_identity.identity_address);
    println!("      身份类型: {:?}", user_identity.identity_type);
    
    // 创建组织身份
    let org_attributes = HashMap::from([
        ("organization_name".to_string(), "智能科技有限公司".to_string()),
        ("registration_number".to_string(), "91110000123456789X".to_string()),
        ("industry".to_string(), "IoT".to_string()),
        ("size".to_string(), "medium".to_string()),
    ]);
    
    let org_identity = blockchain_manager.create_digital_identity(IdentityType::Organization, org_attributes).await?;
    println!("    组织身份已创建:");
    println!("      身份ID: {}", org_identity.identity_id);
    println!("      身份地址: {}", org_identity.identity_address);
    println!("      身份类型: {:?}", org_identity.identity_type);
    
    println!("  验证数字身份...");
    
    // 验证设备身份
    blockchain_manager.verify_digital_identity(&device_identity.identity_id, "verifier_001").await?;
    println!("    设备身份已验证");
    
    // 验证用户身份
    blockchain_manager.verify_digital_identity(&user_identity.identity_id, "verifier_002").await?;
    println!("    用户身份已验证");
    
    // 获取所有数字身份
    let identities = blockchain_manager.get_digital_identities().await;
    println!("  数字身份总数: {}", identities.len());
    for identity in identities {
        println!("    - {} ({:?}): 已验证={}", 
                identity.identity_id, 
                identity.identity_type, 
                identity.is_verified);
    }

    Ok(())
}

/// 供应链溯源演示
async fn demo_supply_chain_tracing() -> Result<(), Box<dyn std::error::Error>> {
    let blockchain_manager = BlockchainIntegrationManager::new(BlockchainConfig {
        blockchain_type: BlockchainType::Ethereum,
        network_url: "https://mainnet.infura.io".to_string(),
        network_id: 1,
        enabled: true,
        connection_timeout: Duration::from_secs(30),
        retry_count: 3,
        retry_interval: Duration::from_secs(5),
        enable_encryption: true,
        private_key_path: None,
        custom_params: HashMap::new(),
    });
    
    println!("  添加供应链溯源记录...");
    
    let product_id = "smart_phone_001";
    let batch_number = "batch_2024_001";
    
    // 生产记录
    let production_record = SupplyChainRecord {
        record_id: uuid::Uuid::new_v4().to_string(),
        product_id: product_id.to_string(),
        batch_number: batch_number.to_string(),
        operation_type: OperationType::Production,
        operation_description: "智能手机生产".to_string(),
        operator: "manufacturer_001".to_string(),
        operation_time: chrono::Utc::now(),
        location: Location {
            latitude: 22.3193,
            longitude: 114.1694,
            address: "深圳市南山区科技园".to_string(),
            city: "深圳".to_string(),
            country: "中国".to_string(),
            postal_code: "518000".to_string(),
        },
        environmental_data: HashMap::from([
            ("temperature".to_string(), 22.5),
            ("humidity".to_string(), 45.0),
            ("air_quality".to_string(), 85.0),
        ]),
        quality_data: HashMap::from([
            ("defect_rate".to_string(), 0.1),
            ("performance_score".to_string(), 95.0),
            ("durability_test".to_string(), 98.0),
        ]),
        transaction_hash: "0xproduction123".to_string(),
        previous_hash: None,
    };
    
    let production_record_id = blockchain_manager.add_supply_chain_record(production_record).await?;
    println!("    生产记录已添加: {}", production_record_id);
    
    // 检验记录
    let inspection_record = SupplyChainRecord {
        record_id: uuid::Uuid::new_v4().to_string(),
        product_id: product_id.to_string(),
        batch_number: batch_number.to_string(),
        operation_type: OperationType::Inspection,
        operation_description: "质量检验".to_string(),
        operator: "inspector_001".to_string(),
        operation_time: chrono::Utc::now(),
        location: Location {
            latitude: 22.3193,
            longitude: 114.1694,
            address: "深圳市南山区质检中心".to_string(),
            city: "深圳".to_string(),
            country: "中国".to_string(),
            postal_code: "518000".to_string(),
        },
        environmental_data: HashMap::new(),
        quality_data: HashMap::from([
            ("inspection_score".to_string(), 97.5),
            ("safety_rating".to_string(), 99.0),
            ("certification".to_string(), 100.0),
        ]),
        transaction_hash: "0xinspection123".to_string(),
        previous_hash: Some("0xproduction123".to_string()),
    };
    
    let inspection_record_id = blockchain_manager.add_supply_chain_record(inspection_record).await?;
    println!("    检验记录已添加: {}", inspection_record_id);
    
    // 运输记录
    let transportation_record = SupplyChainRecord {
        record_id: uuid::Uuid::new_v4().to_string(),
        product_id: product_id.to_string(),
        batch_number: batch_number.to_string(),
        operation_type: OperationType::Transportation,
        operation_description: "产品运输".to_string(),
        operator: "logistics_001".to_string(),
        operation_time: chrono::Utc::now(),
        location: Location {
            latitude: 39.9042,
            longitude: 116.4074,
            address: "北京市朝阳区物流中心".to_string(),
            city: "北京".to_string(),
            country: "中国".to_string(),
            postal_code: "100000".to_string(),
        },
        environmental_data: HashMap::from([
            ("transport_temperature".to_string(), 20.0),
            ("vibration_level".to_string(), 2.5),
            ("shock_events".to_string(), 0.0),
        ]),
        quality_data: HashMap::new(),
        transaction_hash: "0xtransport123".to_string(),
        previous_hash: Some("0xinspection123".to_string()),
    };
    
    let transportation_record_id = blockchain_manager.add_supply_chain_record(transportation_record).await?;
    println!("    运输记录已添加: {}", transportation_record_id);
    
    // 销售记录
    let sale_record = SupplyChainRecord {
        record_id: uuid::Uuid::new_v4().to_string(),
        product_id: product_id.to_string(),
        batch_number: batch_number.to_string(),
        operation_type: OperationType::Sale,
        operation_description: "产品销售".to_string(),
        operator: "retailer_001".to_string(),
        operation_time: chrono::Utc::now(),
        location: Location {
            latitude: 39.9042,
            longitude: 116.4074,
            address: "北京市朝阳区购物中心".to_string(),
            city: "北京".to_string(),
            country: "中国".to_string(),
            postal_code: "100000".to_string(),
        },
        environmental_data: HashMap::new(),
        quality_data: HashMap::from([
            ("customer_satisfaction".to_string(), 96.0),
            ("return_rate".to_string(), 1.5),
        ]),
        transaction_hash: "0xsale123".to_string(),
        previous_hash: Some("0xtransport123".to_string()),
    };
    
    let sale_record_id = blockchain_manager.add_supply_chain_record(sale_record).await?;
    println!("    销售记录已添加: {}", sale_record_id);
    
    println!("  查询供应链溯源记录...");
    
    // 查询产品的完整供应链记录
    let supply_chain_records = blockchain_manager.query_supply_chain_records(product_id).await?;
    println!("    产品 {} 的供应链记录数量: {}", product_id, supply_chain_records.len());
    
    for (i, record) in supply_chain_records.iter().enumerate() {
        println!("      记录 {}: {:?} - {}", i + 1, record.operation_type, record.operation_description);
        println!("        操作者: {}", record.operator);
        println!("        操作时间: {}", record.operation_time.format("%Y-%m-%d %H:%M:%S"));
        println!("        位置: {}, {}", record.location.city, record.location.country);
        println!("        交易哈希: {}", record.transaction_hash);
    }

    Ok(())
}

/// 区块链交易演示
async fn demo_blockchain_transactions() -> Result<(), Box<dyn std::error::Error>> {
    let blockchain_manager = BlockchainIntegrationManager::new(BlockchainConfig {
        blockchain_type: BlockchainType::Ethereum,
        network_url: "https://mainnet.infura.io".to_string(),
        network_id: 1,
        enabled: true,
        connection_timeout: Duration::from_secs(30),
        retry_count: 3,
        retry_interval: Duration::from_secs(5),
        enable_encryption: true,
        private_key_path: None,
        custom_params: HashMap::new(),
    });
    
    println!("  执行区块链交易...");
    
    // 执行转账交易
    let from_address = "0x1234567890123456789012345678901234567890";
    let to_address = "0x0987654321098765432109876543210987654321";
    let amount = 1000000000000000000; // 1 ETH (in wei)
    
    let transfer_hash = blockchain_manager.transfer(from_address, to_address, amount).await?;
    println!("    转账交易已执行:");
    println!("      交易哈希: {}", transfer_hash);
    println!("      发送者: {}", from_address);
    println!("      接收者: {}", to_address);
    println!("      金额: {} wei (1 ETH)", amount);
    
    // 执行更多转账交易
    let transactions = vec![
        ("0x1111111111111111111111111111111111111111", "0x2222222222222222222222222222222222222222", 500000000000000000), // 0.5 ETH
        ("0x3333333333333333333333333333333333333333", "0x4444444444444444444444444444444444444444", 2000000000000000000), // 2 ETH
        ("0x5555555555555555555555555555555555555555", "0x6666666666666666666666666666666666666666", 750000000000000000), // 0.75 ETH
    ];
    
    for (from, to, amount) in transactions {
        let hash = blockchain_manager.transfer(from, to, amount).await?;
        println!("    转账交易: {} -> {} ({} wei) - 哈希: {}", from, to, amount, hash);
    }
    
    // 获取交易历史
    let transaction_history = blockchain_manager.get_transaction_history(Some(5)).await;
    println!("  最近交易历史 ({} 条):", transaction_history.len());
    for (i, transaction) in transaction_history.iter().enumerate() {
        println!("    交易 {}: {} -> {} ({} wei)", 
                i + 1, 
                transaction.from_address, 
                transaction.to_address, 
                transaction.amount);
        println!("      状态: {:?}", transaction.status);
        println!("      交易费用: {} wei", transaction.transaction_fee);
        println!("      时间: {}", transaction.timestamp.format("%H:%M:%S"));
    }

    Ok(())
}

/// 多区块链网络支持演示
async fn demo_multi_blockchain_support() -> Result<(), Box<dyn std::error::Error>> {
    let blockchain_manager = BlockchainIntegrationManager::new(BlockchainConfig {
        blockchain_type: BlockchainType::Ethereum,
        network_url: "https://mainnet.infura.io".to_string(),
        network_id: 1,
        enabled: true,
        connection_timeout: Duration::from_secs(30),
        retry_count: 3,
        retry_interval: Duration::from_secs(5),
        enable_encryption: true,
        private_key_path: None,
        custom_params: HashMap::new(),
    });
    
    println!("  注册多个区块链网络...");
    
    // 注册以太坊主网
    let ethereum_mainnet = BlockchainConfig {
        blockchain_type: BlockchainType::Ethereum,
        network_url: "https://mainnet.infura.io/v3/your-project-id".to_string(),
        network_id: 1,
        enabled: true,
        connection_timeout: Duration::from_secs(30),
        retry_count: 3,
        retry_interval: Duration::from_secs(5),
        enable_encryption: true,
        private_key_path: None,
        custom_params: HashMap::new(),
    };
    blockchain_manager.register_blockchain("ethereum_mainnet".to_string(), ethereum_mainnet).await?;
    println!("    以太坊主网已注册");
    
    // 注册币安智能链
    let bsc_mainnet = BlockchainConfig {
        blockchain_type: BlockchainType::BinanceSmartChain,
        network_url: "https://bsc-dataseed.binance.org".to_string(),
        network_id: 56,
        enabled: true,
        connection_timeout: Duration::from_secs(30),
        retry_count: 3,
        retry_interval: Duration::from_secs(5),
        enable_encryption: true,
        private_key_path: None,
        custom_params: HashMap::new(),
    };
    blockchain_manager.register_blockchain("bsc_mainnet".to_string(), bsc_mainnet).await?;
    println!("    币安智能链已注册");
    
    // 注册多边形网络
    let polygon_mainnet = BlockchainConfig {
        blockchain_type: BlockchainType::Polygon,
        network_url: "https://polygon-rpc.com".to_string(),
        network_id: 137,
        enabled: true,
        connection_timeout: Duration::from_secs(30),
        retry_count: 3,
        retry_interval: Duration::from_secs(5),
        enable_encryption: true,
        private_key_path: None,
        custom_params: HashMap::new(),
    };
    blockchain_manager.register_blockchain("polygon_mainnet".to_string(), polygon_mainnet).await?;
    println!("    多边形网络已注册");
    
    // 注册测试网络
    let ethereum_testnet = BlockchainConfig {
        blockchain_type: BlockchainType::Ethereum,
        network_url: "https://goerli.infura.io/v3/your-project-id".to_string(),
        network_id: 5,
        enabled: true,
        connection_timeout: Duration::from_secs(30),
        retry_count: 3,
        retry_interval: Duration::from_secs(5),
        enable_encryption: true,
        private_key_path: None,
        custom_params: HashMap::new(),
    };
    blockchain_manager.register_blockchain("ethereum_testnet".to_string(), ethereum_testnet).await?;
    println!("    以太坊测试网已注册");
    
    println!("  多区块链网络支持已配置完成");

    Ok(())
}

/// 数据存储和查询演示
async fn demo_data_storage_and_query() -> Result<(), Box<dyn std::error::Error>> {
    let blockchain_manager = BlockchainIntegrationManager::new(BlockchainConfig {
        blockchain_type: BlockchainType::Ethereum,
        network_url: "https://mainnet.infura.io".to_string(),
        network_id: 1,
        enabled: true,
        connection_timeout: Duration::from_secs(30),
        retry_count: 3,
        retry_interval: Duration::from_secs(5),
        enable_encryption: true,
        private_key_path: None,
        custom_params: HashMap::new(),
    });
    
    println!("  数据存储和查询演示...");
    
    // 存储IoT传感器数据
    let sensor_data_records = vec![
        ("temperature_sensor_001", "temperature", 25.5),
        ("humidity_sensor_001", "humidity", 60.0),
        ("pressure_sensor_001", "pressure", 1013.25),
        ("light_sensor_001", "light", 800.0),
        ("motion_sensor_001", "motion", 1.0),
    ];
    
    for (sensor_id, data_type, value) in sensor_data_records {
        let record = SupplyChainRecord {
            record_id: uuid::Uuid::new_v4().to_string(),
            product_id: sensor_id.to_string(),
            batch_number: "data_batch_001".to_string(),
            operation_type: OperationType::DataStorage,
            operation_description: format!("存储{}数据", data_type),
            operator: "data_collector".to_string(),
            operation_time: chrono::Utc::now(),
            location: Location {
                latitude: 39.9042,
                longitude: 116.4074,
                address: "北京市朝阳区数据中心".to_string(),
                city: "北京".to_string(),
                country: "中国".to_string(),
                postal_code: "100000".to_string(),
            },
            environmental_data: HashMap::from([(data_type.to_string(), value)]),
            quality_data: HashMap::new(),
            transaction_hash: format!("0x{}", uuid::Uuid::new_v4().to_string().replace('-', "")),
            previous_hash: None,
        };
        
        let record_id = blockchain_manager.add_supply_chain_record(record).await?;
        println!("    传感器数据已存储: {} = {} (记录ID: {})", sensor_id, value, record_id);
    }
    
    // 查询特定传感器的数据
    let sensor_id = "temperature_sensor_001";
    let sensor_records = blockchain_manager.query_supply_chain_records(sensor_id).await?;
    println!("  查询传感器 {} 的数据记录:", sensor_id);
    for record in sensor_records {
        println!("    记录ID: {}", record.record_id);
        println!("    操作描述: {}", record.operation_description);
        println!("    环境数据: {:?}", record.environmental_data);
        println!("    时间: {}", record.operation_time.format("%Y-%m-%d %H:%M:%S"));
    }

    Ok(())
}

/// 区块链统计和报告演示
async fn demo_blockchain_statistics() -> Result<(), Box<dyn std::error::Error>> {
    let blockchain_manager = BlockchainIntegrationManager::new(BlockchainConfig {
        blockchain_type: BlockchainType::Ethereum,
        network_url: "https://mainnet.infura.io".to_string(),
        network_id: 1,
        enabled: true,
        connection_timeout: Duration::from_secs(30),
        retry_count: 3,
        retry_interval: Duration::from_secs(5),
        enable_encryption: true,
        private_key_path: None,
        custom_params: HashMap::new(),
    });
    
    println!("  生成区块链统计报告...");
    
    // 执行一些操作以生成统计数据
    // 部署智能合约
    let contract_config = SmartContractConfig {
        contract_address: "".to_string(),
        contract_abi: "[]".to_string(),
        contract_name: "StatsContract".to_string(),
        contract_version: "1.0".to_string(),
        network: "mainnet".to_string(),
        deployer_address: "0xdeployer".to_string(),
        gas_limit: 1000000,
        gas_price: 20000000000,
        custom_params: HashMap::new(),
    };
    let _ = blockchain_manager.deploy_smart_contract(contract_config).await?;
    
    // 执行转账
    for i in 0..3 {
        let _ = blockchain_manager.transfer(
            &format!("0x{}", "1".repeat(40)),
            &format!("0x{}", "2".repeat(40)),
            1000000000000000000 + i * 100000000000000000
        ).await?;
    }
    
    // 创建数字身份
    let attributes = HashMap::from([("name".to_string(), "Test Device".to_string())]);
    let _ = blockchain_manager.create_digital_identity(IdentityType::Device, attributes).await?;
    
    // 添加供应链记录
    let record = SupplyChainRecord {
        record_id: uuid::Uuid::new_v4().to_string(),
        product_id: "test_product".to_string(),
        batch_number: "test_batch".to_string(),
        operation_type: OperationType::Production,
        operation_description: "测试生产".to_string(),
        operator: "test_operator".to_string(),
        operation_time: chrono::Utc::now(),
        location: Location {
            latitude: 39.9042,
            longitude: 116.4074,
            address: "测试地址".to_string(),
            city: "北京".to_string(),
            country: "中国".to_string(),
            postal_code: "100000".to_string(),
        },
        environmental_data: HashMap::new(),
        quality_data: HashMap::new(),
        transaction_hash: "0xtest".to_string(),
        previous_hash: None,
    };
    let _ = blockchain_manager.add_supply_chain_record(record).await?;
    
    // 获取统计信息
    let stats = blockchain_manager.get_stats().await;
    println!("  区块链统计报告:");
    println!("    总交易数: {}", stats.total_transactions);
    println!("    成功交易数: {}", stats.successful_transactions);
    println!("    失败交易数: {}", stats.failed_transactions);
    println!("    平均交易时间: {:?}", stats.avg_transaction_time);
    println!("    总Gas使用量: {}", stats.total_gas_used);
    println!("    总交易费用: {} wei", stats.total_transaction_fees);
    println!("    数字身份数量: {}", stats.digital_identity_count);
    println!("    供应链记录数量: {}", stats.supply_chain_record_count);
    println!("    最后更新时间: {}", stats.last_updated.format("%Y-%m-%d %H:%M:%S"));
    
    // 获取交易历史
    let transaction_history = blockchain_manager.get_transaction_history(Some(5)).await;
    println!("  最近交易历史 ({} 条):", transaction_history.len());
    for (i, transaction) in transaction_history.iter().enumerate() {
        println!("    交易 {}: {:?} - {} -> {}", 
                i + 1, 
                transaction.transaction_type,
                transaction.from_address, 
                transaction.to_address);
        println!("      状态: {:?}, 金额: {} wei, 费用: {} wei", 
                transaction.status, 
                transaction.amount, 
                transaction.transaction_fee);
    }
    
    // 获取智能合约列表
    let contracts = blockchain_manager.get_smart_contracts().await;
    println!("  已部署的智能合约 ({} 个):", contracts.len());
    for contract in contracts {
        println!("    - {}: {}", contract.contract_name, contract.contract_address);
    }
    
    // 获取数字身份列表
    let identities = blockchain_manager.get_digital_identities().await;
    println!("  数字身份 ({} 个):", identities.len());
    for identity in identities {
        println!("    - {} ({:?}): 已验证={}", 
                identity.identity_id, 
                identity.identity_type, 
                identity.is_verified);
    }

    Ok(())
}
