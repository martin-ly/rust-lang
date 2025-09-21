//! 高级边缘计算演示示例
//! 
//! 展示如何使用c17_iot的高级边缘计算功能进行分布式计算、边缘AI推理和实时决策

use c17_iot::edge_computing_advanced::{
    EdgeComputingManager, EdgeComputingConfig, EdgeNode, EdgeCluster, EdgeTask,
    EdgeNodeType, EdgeTaskType, EdgeNodeStatus, EdgeTaskStatus, TaskPriority,
    ComputeCapacity, NetworkCapacity, StorageCapacity, LoadBalancingStrategy,
    FaultToleranceStrategy, Location, EdgeNodeConfig, EdgeTaskConfig, ResourceRequirements,
    StorageType
};
use std::time::Duration;
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动高级边缘计算演示...");

    println!("📊 开始演示IoT系统高级边缘计算功能...");

    // 1. 边缘计算管理器创建和配置
    println!("\n1️⃣ 边缘计算管理器创建和配置");
    demo_edge_manager_creation().await?;

    // 2. 边缘集群创建和管理
    println!("\n2️⃣ 边缘集群创建和管理");
    demo_edge_cluster_management().await?;

    // 3. 边缘节点管理
    println!("\n3️⃣ 边缘节点管理");
    demo_edge_node_management().await?;

    // 4. 任务调度和执行
    println!("\n4️⃣ 任务调度和执行");
    demo_task_scheduling().await?;

    // 5. 负载均衡
    println!("\n5️⃣ 负载均衡");
    demo_load_balancing().await?;

    // 6. 容错处理
    println!("\n6️⃣ 容错处理");
    demo_fault_tolerance().await?;

    // 7. 边缘AI推理
    println!("\n7️⃣ 边缘AI推理");
    demo_edge_ai_inference().await?;

    // 8. 实时决策引擎
    println!("\n8️⃣ 实时决策引擎");
    demo_realtime_decision_engine().await?;

    // 9. 边缘统计和监控
    println!("\n9️⃣ 边缘统计和监控");
    demo_edge_statistics().await?;

    println!("\n✅ 高级边缘计算演示完成!");
    println!("🎯 演示展示了以下功能:");
    println!("  - 边缘集群管理");
    println!("  - 边缘节点管理");
    println!("  - 任务调度和执行");
    println!("  - 负载均衡和容错");
    println!("  - 边缘AI推理");
    println!("  - 实时决策引擎");

    Ok(())
}

/// 边缘计算管理器创建和配置演示
async fn demo_edge_manager_creation() -> Result<(), Box<dyn std::error::Error>> {
    // 创建边缘计算配置
    let config = EdgeComputingConfig {
        enable_edge_computing: true,
        max_clusters: 10,
        max_nodes_per_cluster: 100,
        task_scheduling_interval: Duration::from_secs(5),
        default_load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
        default_fault_tolerance_strategy: FaultToleranceStrategy::TaskRetry,
        enable_auto_scaling: true,
        auto_scaling_threshold: 0.8,
        custom_params: HashMap::new(),
    };

    println!("  创建边缘计算管理器...");
    let edge_manager = EdgeComputingManager::new(config);
    
    // 获取初始统计信息
    let stats = edge_manager.get_stats().await;
    println!("  初始边缘计算统计:");
    println!("    总集群数: {}", stats.total_clusters);
    println!("    总节点数: {}", stats.total_nodes);
    println!("    在线节点数: {}", stats.online_nodes);
    println!("    总任务数: {}", stats.total_tasks);
    println!("    成功任务数: {}", stats.successful_tasks);
    println!("    失败任务数: {}", stats.failed_tasks);
    println!("    平均任务执行时间: {:?}", stats.avg_task_execution_time);
    println!("    平均资源利用率: {:.2}%", stats.avg_resource_utilization * 100.0);

    Ok(())
}

/// 边缘集群创建和管理演示
async fn demo_edge_cluster_management() -> Result<(), Box<dyn std::error::Error>> {
    let edge_manager = EdgeComputingManager::new(EdgeComputingConfig::default());
    
    println!("  创建边缘集群...");
    
    // 创建边缘节点
    let nodes = vec![
        create_edge_node("node1", "边缘服务器1", EdgeNodeType::EdgeServer, 8, 16384, 2),
        create_edge_node("node2", "边缘服务器2", EdgeNodeType::EdgeServer, 8, 16384, 2),
        create_edge_node("node3", "边缘AI节点1", EdgeNodeType::EdgeAINode, 16, 32768, 4),
        create_edge_node("node4", "边缘存储节点1", EdgeNodeType::EdgeStorageNode, 4, 8192, 0),
        create_edge_node("node5", "网关节点1", EdgeNodeType::GatewayNode, 2, 4096, 0),
    ];
    
    // 创建边缘集群
    let cluster = EdgeCluster {
        cluster_id: "beijing_cluster".to_string(),
        cluster_name: "北京边缘集群".to_string(),
        nodes,
        status: c17_iot::edge_computing_advanced::ClusterStatus::Healthy,
        load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
        fault_tolerance_strategy: FaultToleranceStrategy::TaskRetry,
        created_at: chrono::Utc::now(),
        last_updated: chrono::Utc::now(),
    };
    
    let cluster_id = edge_manager.create_cluster(cluster).await?;
    println!("    边缘集群已创建: {}", cluster_id);
    
    // 创建第二个集群
    let nodes2 = vec![
        create_edge_node("node6", "边缘服务器3", EdgeNodeType::EdgeServer, 12, 24576, 3),
        create_edge_node("node7", "边缘AI节点2", EdgeNodeType::EdgeAINode, 20, 40960, 6),
        create_edge_node("node8", "边缘存储节点2", EdgeNodeType::EdgeStorageNode, 6, 12288, 0),
    ];
    
    let cluster2 = EdgeCluster {
        cluster_id: "shanghai_cluster".to_string(),
        cluster_name: "上海边缘集群".to_string(),
        nodes: nodes2,
        status: c17_iot::edge_computing_advanced::ClusterStatus::Healthy,
        load_balancing_strategy: LoadBalancingStrategy::WeightedRoundRobin,
        fault_tolerance_strategy: FaultToleranceStrategy::NodeFailover,
        created_at: chrono::Utc::now(),
        last_updated: chrono::Utc::now(),
    };
    
    let cluster_id2 = edge_manager.create_cluster(cluster2).await?;
    println!("    边缘集群已创建: {}", cluster_id2);
    
    // 获取集群信息
    let cluster_info = edge_manager.get_cluster_info(&cluster_id).await?;
    println!("  集群信息:");
    println!("    集群名称: {}", cluster_info.cluster_name);
    println!("    节点数量: {}", cluster_info.nodes.len());
    println!("    集群状态: {:?}", cluster_info.status);
    println!("    负载均衡策略: {:?}", cluster_info.load_balancing_strategy);
    println!("    容错策略: {:?}", cluster_info.fault_tolerance_strategy);
    
    // 显示节点信息
    for node in &cluster_info.nodes {
        println!("      节点: {} ({:?}) - CPU: {}核, 内存: {}MB, GPU: {}个", 
                node.node_name, 
                node.node_type, 
                node.compute_capacity.cpu_cores,
                node.compute_capacity.memory_size,
                node.compute_capacity.gpu_count);
    }

    Ok(())
}

/// 边缘节点管理演示
async fn demo_edge_node_management() -> Result<(), Box<dyn std::error::Error>> {
    let edge_manager = EdgeComputingManager::new(EdgeComputingConfig::default());
    
    println!("  管理边缘节点...");
    
    // 创建初始集群
    let initial_cluster = EdgeCluster {
        cluster_id: "test_cluster".to_string(),
        cluster_name: "测试集群".to_string(),
        nodes: vec![],
        status: c17_iot::edge_computing_advanced::ClusterStatus::Healthy,
        load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
        fault_tolerance_strategy: FaultToleranceStrategy::TaskRetry,
        created_at: chrono::Utc::now(),
        last_updated: chrono::Utc::now(),
    };
    
    edge_manager.create_cluster(initial_cluster).await?;
    
    // 添加不同类型的节点
    let node_types = vec![
        (EdgeNodeType::SensorNode, "传感器节点", 1, 512, 0),
        (EdgeNodeType::GatewayNode, "网关节点", 2, 1024, 0),
        (EdgeNodeType::EdgeServer, "边缘服务器", 8, 8192, 1),
        (EdgeNodeType::EdgeAINode, "边缘AI节点", 16, 16384, 4),
        (EdgeNodeType::EdgeStorageNode, "边缘存储节点", 4, 4096, 0),
    ];
    
    for (i, (node_type, name, cpu, memory, gpu)) in node_types.iter().enumerate() {
        let node = create_edge_node(
            &format!("node{}", i + 1),
            name,
            node_type.clone(),
            *cpu,
            *memory,
            *gpu,
        );
        
        edge_manager.add_node_to_cluster("test_cluster", node).await?;
        println!("    添加节点: {} ({:?})", name, node_type);
    }
    
    // 获取更新后的集群信息
    let cluster_info = edge_manager.get_cluster_info("test_cluster").await?;
    println!("  集群节点统计:");
    println!("    总节点数: {}", cluster_info.nodes.len());
    
    let mut node_type_count = HashMap::new();
    for node in &cluster_info.nodes {
        *node_type_count.entry(&node.node_type).or_insert(0) += 1;
    }
    
    for (node_type, count) in node_type_count {
        println!("    {:?}: {} 个", node_type, count);
    }
    
    // 显示节点资源统计
    let total_cpu: u32 = cluster_info.nodes.iter().map(|n| n.compute_capacity.cpu_cores).sum();
    let total_memory: u64 = cluster_info.nodes.iter().map(|n| n.compute_capacity.memory_size).sum();
    let total_gpu: u32 = cluster_info.nodes.iter().map(|n| n.compute_capacity.gpu_count).sum();
    
    println!("  集群资源统计:");
    println!("    总CPU核心数: {}", total_cpu);
    println!("    总内存: {} MB", total_memory);
    println!("    总GPU数: {}", total_gpu);

    Ok(())
}

/// 任务调度和执行演示
async fn demo_task_scheduling() -> Result<(), Box<dyn std::error::Error>> {
    let edge_manager = EdgeComputingManager::new(EdgeComputingConfig::default());
    
    println!("  任务调度和执行...");
    
    // 创建集群和节点
    let cluster = EdgeCluster {
        cluster_id: "scheduling_cluster".to_string(),
        cluster_name: "调度测试集群".to_string(),
        nodes: vec![
            create_edge_node("sched_node1", "调度节点1", EdgeNodeType::EdgeServer, 4, 4096, 0),
            create_edge_node("sched_node2", "调度节点2", EdgeNodeType::EdgeServer, 8, 8192, 1),
            create_edge_node("sched_node3", "调度节点3", EdgeNodeType::EdgeAINode, 16, 16384, 2),
        ],
        status: c17_iot::edge_computing_advanced::ClusterStatus::Healthy,
        load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
        fault_tolerance_strategy: FaultToleranceStrategy::TaskRetry,
        created_at: chrono::Utc::now(),
        last_updated: chrono::Utc::now(),
    };
    
    edge_manager.create_cluster(cluster).await?;
    
    // 创建不同优先级的任务
    let tasks = vec![
        create_edge_task("task1", EdgeTaskType::DataProcessing, TaskPriority::Low, 2, 1024, false),
        create_edge_task("task2", EdgeTaskType::AIInference, TaskPriority::High, 4, 2048, true),
        create_edge_task("task3", EdgeTaskType::RealTimeDecision, TaskPriority::Critical, 1, 512, false),
        create_edge_task("task4", EdgeTaskType::DataAggregation, TaskPriority::Normal, 2, 1024, false),
        create_edge_task("task5", EdgeTaskType::AIInference, TaskPriority::High, 8, 4096, true),
    ];
    
    println!("    提交任务到调度队列...");
    for task in tasks {
        let task_id = edge_manager.submit_task(task).await?;
        println!("      任务已提交: {}", task_id);
    }
    
    // 等待任务调度和执行
    println!("    等待任务调度和执行...");
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    // 检查任务状态
    let all_tasks = edge_manager.get_tasks(None, None).await;
    println!("  任务执行状态:");
    for task in all_tasks {
        println!("    任务 {}: {:?} - 优先级: {:?}, 类型: {:?}", 
                task.task_id, 
                task.status, 
                task.priority, 
                task.task_type);
        if let Some(node) = task.assigned_node {
            println!("      分配节点: {}", node);
        }
        if let Some(execution_time) = task.execution_time {
            println!("      执行时间: {:?}", execution_time);
        }
    }

    Ok(())
}

/// 负载均衡演示
async fn demo_load_balancing() -> Result<(), Box<dyn std::error::Error>> {
    let edge_manager = EdgeComputingManager::new(EdgeComputingConfig::default());
    
    println!("  负载均衡演示...");
    
    // 创建具有不同负载均衡策略的集群
    let strategies = vec![
        (LoadBalancingStrategy::RoundRobin, "轮询策略"),
        (LoadBalancingStrategy::LeastConnections, "最少连接策略"),
        (LoadBalancingStrategy::WeightedRoundRobin, "加权轮询策略"),
        (LoadBalancingStrategy::ResourceBased, "基于资源策略"),
    ];
    
    for (i, (strategy, description)) in strategies.iter().enumerate() {
        let cluster = EdgeCluster {
            cluster_id: format!("lb_cluster_{}", i + 1),
            cluster_name: format!("负载均衡集群 {}", i + 1),
            nodes: vec![
                create_edge_node(&format!("lb_node{}_1", i + 1), &format!("节点{}_1", i + 1), EdgeNodeType::EdgeServer, 4, 4096, 0),
                create_edge_node(&format!("lb_node{}_2", i + 1), &format!("节点{}_2", i + 1), EdgeNodeType::EdgeServer, 6, 6144, 1),
                create_edge_node(&format!("lb_node{}_3", i + 1), &format!("节点{}_3", i + 1), EdgeNodeType::EdgeServer, 8, 8192, 2),
            ],
            status: c17_iot::edge_computing_advanced::ClusterStatus::Healthy,
            load_balancing_strategy: strategy.clone(),
            fault_tolerance_strategy: FaultToleranceStrategy::TaskRetry,
            created_at: chrono::Utc::now(),
            last_updated: chrono::Utc::now(),
        };
        
        edge_manager.create_cluster(cluster).await?;
        println!("    创建集群: {} ({})", format!("负载均衡集群 {}", i + 1), description);
    }
    
    // 为每个集群提交任务
    for i in 1..=4 {
        let cluster_id = format!("lb_cluster_{}", i);
        let cluster_info = edge_manager.get_cluster_info(&cluster_id).await?;
        
        println!("  {} 任务分配:", cluster_info.cluster_name);
        
        // 提交多个任务
        for j in 1..=6 {
            let task = create_edge_task(
                &format!("lb_task_{}_{}", i, j),
                EdgeTaskType::DataProcessing,
                TaskPriority::Normal,
                2,
                1024,
                false,
            );
            
            edge_manager.submit_task(task).await?;
        }
        
        // 等待任务调度
        tokio::time::sleep(Duration::from_millis(500)).await;
        
        // 检查任务分配情况
        let tasks = edge_manager.get_tasks(None, None).await;
        let cluster_tasks: Vec<_> = tasks.iter()
            .filter(|t| t.task_id.starts_with(&format!("lb_task_{}_", i)))
            .collect();
        
        let mut node_task_count = HashMap::new();
        for task in cluster_tasks {
            if let Some(node) = &task.assigned_node {
                *node_task_count.entry(node.clone()).or_insert(0) += 1;
            }
        }
        
        for (node, count) in node_task_count {
            println!("    节点 {}: {} 个任务", node, count);
        }
    }

    Ok(())
}

/// 容错处理演示
async fn demo_fault_tolerance() -> Result<(), Box<dyn std::error::Error>> {
    let edge_manager = EdgeComputingManager::new(EdgeComputingConfig::default());
    
    println!("  容错处理演示...");
    
    // 创建具有不同容错策略的集群
    let strategies = vec![
        (FaultToleranceStrategy::None, "无容错"),
        (FaultToleranceStrategy::TaskRetry, "任务重试"),
        (FaultToleranceStrategy::NodeFailover, "节点切换"),
        (FaultToleranceStrategy::DataReplication, "数据复制"),
    ];
    
    for (i, (strategy, description)) in strategies.iter().enumerate() {
        let cluster = EdgeCluster {
            cluster_id: format!("ft_cluster_{}", i + 1),
            cluster_name: format!("容错集群 {}", i + 1),
            nodes: vec![
                create_edge_node(&format!("ft_node{}_1", i + 1), &format!("主节点{}", i + 1), EdgeNodeType::EdgeServer, 4, 4096, 0),
                create_edge_node(&format!("ft_node{}_2", i + 1), &format!("备用节点{}", i + 1), EdgeNodeType::EdgeServer, 4, 4096, 0),
            ],
            status: c17_iot::edge_computing_advanced::ClusterStatus::Healthy,
            load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
            fault_tolerance_strategy: strategy.clone(),
            created_at: chrono::Utc::now(),
            last_updated: chrono::Utc::now(),
        };
        
        edge_manager.create_cluster(cluster).await?;
        println!("    创建集群: {} ({})", format!("容错集群 {}", i + 1), description);
    }
    
    // 模拟节点故障和恢复
    println!("  模拟节点故障和恢复...");
    
    for i in 1..=4 {
        let cluster_id = format!("ft_cluster_{}", i);
        let mut cluster_info = edge_manager.get_cluster_info(&cluster_id).await?;
        
        println!("  {} 故障模拟:", cluster_info.cluster_name);
        
        // 模拟主节点故障
        if let Some(main_node) = cluster_info.nodes.get_mut(0) {
            main_node.status = EdgeNodeStatus::Error("模拟故障".to_string());
            println!("    主节点故障: {}", main_node.node_name);
        }
        
        // 提交任务测试容错
        let task = create_edge_task(
            &format!("ft_task_{}", i),
            EdgeTaskType::DataProcessing,
            TaskPriority::High,
            2,
            1024,
            false,
        );
        
        edge_manager.submit_task(task).await?;
        
        // 等待任务处理
        tokio::time::sleep(Duration::from_millis(500)).await;
        
        // 检查任务状态
        let tasks = edge_manager.get_tasks(None, None).await;
        let ft_task = tasks.iter().find(|t| t.task_id == format!("ft_task_{}", i));
        
        if let Some(task) = ft_task {
            println!("    任务状态: {:?}", task.status);
            if let Some(node) = &task.assigned_node {
                println!("    分配节点: {}", node);
            }
        }
        
        // 恢复节点
        if let Some(main_node) = cluster_info.nodes.get_mut(0) {
            main_node.status = EdgeNodeStatus::Online;
            println!("    主节点恢复: {}", main_node.node_name);
        }
    }

    Ok(())
}

/// 边缘AI推理演示
async fn demo_edge_ai_inference() -> Result<(), Box<dyn std::error::Error>> {
    let edge_manager = EdgeComputingManager::new(EdgeComputingConfig::default());
    
    println!("  边缘AI推理演示...");
    
    // 创建AI推理集群
    let ai_cluster = EdgeCluster {
        cluster_id: "ai_cluster".to_string(),
        cluster_name: "AI推理集群".to_string(),
        nodes: vec![
            create_edge_node("ai_node1", "AI推理节点1", EdgeNodeType::EdgeAINode, 16, 32768, 4),
            create_edge_node("ai_node2", "AI推理节点2", EdgeNodeType::EdgeAINode, 20, 40960, 6),
            create_edge_node("ai_node3", "AI推理节点3", EdgeNodeType::EdgeAINode, 24, 49152, 8),
        ],
        status: c17_iot::edge_computing_advanced::ClusterStatus::Healthy,
        load_balancing_strategy: LoadBalancingStrategy::ResourceBased,
        fault_tolerance_strategy: FaultToleranceStrategy::NodeFailover,
        created_at: chrono::Utc::now(),
        last_updated: chrono::Utc::now(),
    };
    
    edge_manager.create_cluster(ai_cluster).await?;
    
    // 创建不同类型的AI推理任务
    let ai_tasks = vec![
        ("图像识别", EdgeTaskType::AIInference, 4, 2048, true),
        ("语音识别", EdgeTaskType::AIInference, 2, 1024, false),
        ("自然语言处理", EdgeTaskType::AIInference, 8, 4096, true),
        ("视频分析", EdgeTaskType::AIInference, 12, 8192, true),
        ("异常检测", EdgeTaskType::AIInference, 2, 1024, false),
    ];
    
    println!("    提交AI推理任务...");
    for (task_name, task_type, cpu, memory, gpu_required) in ai_tasks {
        let task = EdgeTask {
            task_id: format!("ai_task_{}", task_name.replace(" ", "_")),
            task_type: task_type.clone(),
            status: EdgeTaskStatus::Pending,
            priority: TaskPriority::High,
            input_data: HashMap::from([
                ("model_type".to_string(), task_name.to_string()),
                ("input_size".to_string(), "1024x1024".to_string()),
                ("batch_size".to_string(), "32".to_string()),
            ]),
            output_data: None,
            assigned_node: None,
            created_at: chrono::Utc::now(),
            started_at: None,
            completed_at: None,
            execution_time: None,
            error_message: None,
            config: EdgeTaskConfig {
                max_execution_time: Duration::from_secs(300),
                retry_count: 3,
                enable_fault_tolerance: true,
                enable_load_balancing: true,
                resource_requirements: ResourceRequirements {
                    cpu_cores: cpu,
                    memory,
                    gpu_required,
                    storage: 500,
                    network_bandwidth: 1000,
                },
                custom_params: HashMap::from([
                    ("model_path".to_string(), format!("/models/{}", task_name)),
                    ("precision".to_string(), "fp16".to_string()),
                ]),
            },
        };
        
        let task_id = edge_manager.submit_task(task).await?;
        println!("      AI任务已提交: {} ({})", task_id, task_name);
    }
    
    // 等待AI任务执行
    println!("    等待AI推理任务执行...");
    tokio::time::sleep(Duration::from_secs(3)).await;
    
    // 检查AI任务执行状态
    let ai_tasks = edge_manager.get_tasks(Some(EdgeTaskStatus::Running), None).await;
    println!("  运行中的AI任务:");
    for task in ai_tasks {
        if task.task_type == EdgeTaskType::AIInference {
            println!("    任务: {} - 状态: {:?}", task.task_id, task.status);
            if let Some(node) = &task.assigned_node {
                println!("      分配节点: {}", node);
            }
            if let Some(model_type) = task.input_data.get("model_type") {
                println!("      模型类型: {}", model_type);
            }
        }
    }

    Ok(())
}

/// 实时决策引擎演示
async fn demo_realtime_decision_engine() -> Result<(), Box<dyn std::error::Error>> {
    let edge_manager = EdgeComputingManager::new(EdgeComputingConfig::default());
    
    println!("  实时决策引擎演示...");
    
    // 创建实时决策集群
    let decision_cluster = EdgeCluster {
        cluster_id: "decision_cluster".to_string(),
        cluster_name: "实时决策集群".to_string(),
        nodes: vec![
            create_edge_node("decision_node1", "决策节点1", EdgeNodeType::EdgeServer, 8, 8192, 1),
            create_edge_node("decision_node2", "决策节点2", EdgeNodeType::EdgeServer, 8, 8192, 1),
            create_edge_node("decision_node3", "决策节点3", EdgeNodeType::EdgeServer, 8, 8192, 1),
        ],
        status: c17_iot::edge_computing_advanced::ClusterStatus::Healthy,
        load_balancing_strategy: LoadBalancingStrategy::LeastConnections,
        fault_tolerance_strategy: FaultToleranceStrategy::TaskRetry,
        created_at: chrono::Utc::now(),
        last_updated: chrono::Utc::now(),
    };
    
    edge_manager.create_cluster(decision_cluster).await?;
    
    // 创建实时决策任务
    let decision_scenarios = vec![
        ("交通信号控制", "实时调整交通信号灯"),
        ("智能电网调度", "实时调整电力分配"),
        ("环境监测响应", "实时响应环境变化"),
        ("安全监控告警", "实时安全威胁检测"),
        ("设备故障预测", "实时设备健康监测"),
    ];
    
    println!("    提交实时决策任务...");
    for (scenario, description) in decision_scenarios {
        let task = EdgeTask {
            task_id: format!("decision_task_{}", scenario.replace(" ", "_")),
            task_type: EdgeTaskType::RealTimeDecision,
            status: EdgeTaskStatus::Pending,
            priority: TaskPriority::Critical,
            input_data: HashMap::from([
                ("scenario".to_string(), scenario.to_string()),
                ("description".to_string(), description.to_string()),
                ("response_time_requirement".to_string(), "100ms".to_string()),
                ("decision_confidence".to_string(), "0.95".to_string()),
            ]),
            output_data: None,
            assigned_node: None,
            created_at: chrono::Utc::now(),
            started_at: None,
            completed_at: None,
            execution_time: None,
            error_message: None,
            config: EdgeTaskConfig {
                max_execution_time: Duration::from_millis(100), // 100ms超时
                retry_count: 5,
                enable_fault_tolerance: true,
                enable_load_balancing: true,
                resource_requirements: ResourceRequirements {
                    cpu_cores: 2,
                    memory: 1024,
                    gpu_required: false,
                    storage: 100,
                    network_bandwidth: 100,
                },
                custom_params: HashMap::from([
                    ("decision_algorithm".to_string(), "rule_based".to_string()),
                    ("update_frequency".to_string(), "10Hz".to_string()),
                ]),
            },
        };
        
        let task_id = edge_manager.submit_task(task).await?;
        println!("      决策任务已提交: {} ({})", task_id, scenario);
    }
    
    // 等待决策任务执行
    println!("    等待实时决策任务执行...");
    tokio::time::sleep(Duration::from_millis(500)).await;
    
    // 检查决策任务执行状态
    let decision_tasks = edge_manager.get_tasks(Some(EdgeTaskStatus::Running), None).await;
    println!("  运行中的决策任务:");
    for task in decision_tasks {
        if task.task_type == EdgeTaskType::RealTimeDecision {
            println!("    任务: {} - 状态: {:?}", task.task_id, task.status);
            if let Some(node) = &task.assigned_node {
                println!("      分配节点: {}", node);
            }
            if let Some(scenario) = task.input_data.get("scenario") {
                println!("      决策场景: {}", scenario);
            }
            if let Some(response_time) = task.input_data.get("response_time_requirement") {
                println!("      响应时间要求: {}", response_time);
            }
        }
    }

    Ok(())
}

/// 边缘统计和监控演示
async fn demo_edge_statistics() -> Result<(), Box<dyn std::error::Error>> {
    let edge_manager = EdgeComputingManager::new(EdgeComputingConfig::default());
    
    println!("  生成边缘统计报告...");
    
    // 执行一些操作以生成统计数据
    // 创建集群
    let cluster = EdgeCluster {
        cluster_id: "stats_cluster".to_string(),
        cluster_name: "统计测试集群".to_string(),
        nodes: vec![
            create_edge_node("stats_node1", "统计节点1", EdgeNodeType::EdgeServer, 4, 4096, 0),
            create_edge_node("stats_node2", "统计节点2", EdgeNodeType::EdgeServer, 6, 6144, 1),
        ],
        status: c17_iot::edge_computing_advanced::ClusterStatus::Healthy,
        load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
        fault_tolerance_strategy: FaultToleranceStrategy::TaskRetry,
        created_at: chrono::Utc::now(),
        last_updated: chrono::Utc::now(),
    };
    
    edge_manager.create_cluster(cluster).await?;
    
    // 提交一些任务
    for i in 1..=10 {
        let task = create_edge_task(
            &format!("stats_task_{}", i),
            EdgeTaskType::DataProcessing,
            TaskPriority::Normal,
            2,
            1024,
            false,
        );
        
        edge_manager.submit_task(task).await?;
    }
    
    // 等待任务执行
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    // 获取统计信息
    let stats = edge_manager.get_stats().await;
    println!("  边缘计算统计报告:");
    println!("    总集群数: {}", stats.total_clusters);
    println!("    总节点数: {}", stats.total_nodes);
    println!("    在线节点数: {}", stats.online_nodes);
    println!("    总任务数: {}", stats.total_tasks);
    println!("    成功任务数: {}", stats.successful_tasks);
    println!("    失败任务数: {}", stats.failed_tasks);
    println!("    平均任务执行时间: {:?}", stats.avg_task_execution_time);
    println!("    平均资源利用率: {:.2}%", stats.avg_resource_utilization * 100.0);
    println!("    最后更新时间: {}", stats.last_updated.format("%Y-%m-%d %H:%M:%S"));
    
    // 获取任务列表
    let all_tasks = edge_manager.get_tasks(None, Some(10)).await;
    println!("  最近任务 ({} 个):", all_tasks.len());
    for (i, task) in all_tasks.iter().enumerate() {
        println!("    {}: {} - {:?} ({:?})", 
                i + 1, 
                task.task_id, 
                task.status, 
                task.task_type);
        if let Some(node) = &task.assigned_node {
            println!("      分配节点: {}", node);
        }
        if let Some(execution_time) = task.execution_time {
            println!("      执行时间: {:?}", execution_time);
        }
    }
    
    // 按状态统计任务
    let pending_tasks = edge_manager.get_tasks(Some(EdgeTaskStatus::Pending), None).await;
    let running_tasks = edge_manager.get_tasks(Some(EdgeTaskStatus::Running), None).await;
    let completed_tasks = edge_manager.get_tasks(Some(EdgeTaskStatus::Completed), None).await;
    let failed_tasks = edge_manager.get_tasks(Some(EdgeTaskStatus::Failed), None).await;
    
    println!("  任务状态统计:");
    println!("    等待中: {} 个", pending_tasks.len());
    println!("    运行中: {} 个", running_tasks.len());
    println!("    已完成: {} 个", completed_tasks.len());
    println!("    失败: {} 个", failed_tasks.len());

    Ok(())
}

/// 创建边缘节点的辅助函数
fn create_edge_node(id: &str, name: &str, node_type: EdgeNodeType, cpu_cores: u32, memory_size: u64, gpu_count: u32) -> EdgeNode {
    EdgeNode {
        node_id: id.to_string(),
        node_name: name.to_string(),
        node_type,
        status: EdgeNodeStatus::Online,
        compute_capacity: ComputeCapacity {
            cpu_cores,
            cpu_frequency: 2400,
            memory_size,
            gpu_count,
            gpu_memory: (gpu_count * 4096) as u64,
            performance_score: 0.8 + (cpu_cores as f64 * 0.01),
        },
        network_capacity: NetworkCapacity {
            bandwidth: 1000,
            latency: 10,
            supported_protocols: vec!["TCP".to_string(), "UDP".to_string(), "HTTP".to_string()],
            quality_score: 0.9,
        },
        storage_capacity: StorageCapacity {
            storage_size: 1000,
            available_storage: 800,
            storage_type: StorageType::SSD,
            read_write_speed: 500,
        },
        location: Location {
            latitude: 39.9042 + (rand::random::<f64>() - 0.5) * 0.1,
            longitude: 116.4074 + (rand::random::<f64>() - 0.5) * 0.1,
            altitude: 50.0,
            region_id: "beijing".to_string(),
            region_name: "北京".to_string(),
        },
        created_at: chrono::Utc::now(),
        last_updated: chrono::Utc::now(),
        config: EdgeNodeConfig {
            max_concurrent_tasks: 10,
            task_timeout: Duration::from_secs(300),
            enable_ai_inference: true,
            enable_realtime_decision: true,
            enable_data_cache: true,
            cache_size: 1024,
            custom_params: HashMap::new(),
        },
    }
}

/// 创建边缘任务的辅助函数
fn create_edge_task(id: &str, task_type: EdgeTaskType, priority: TaskPriority, cpu_cores: u32, memory: u64, gpu_required: bool) -> EdgeTask {
    EdgeTask {
        task_id: id.to_string(),
        task_type,
        status: EdgeTaskStatus::Pending,
        priority,
        input_data: HashMap::from([
            ("task_id".to_string(), id.to_string()),
            ("timestamp".to_string(), chrono::Utc::now().to_rfc3339()),
        ]),
        output_data: None,
        assigned_node: None,
        created_at: chrono::Utc::now(),
        started_at: None,
        completed_at: None,
        execution_time: None,
        error_message: None,
        config: EdgeTaskConfig {
            max_execution_time: Duration::from_secs(60),
            retry_count: 3,
            enable_fault_tolerance: true,
            enable_load_balancing: true,
            resource_requirements: ResourceRequirements {
                cpu_cores,
                memory,
                gpu_required,
                storage: 100,
                network_bandwidth: 100,
            },
            custom_params: HashMap::new(),
        },
    }
}
