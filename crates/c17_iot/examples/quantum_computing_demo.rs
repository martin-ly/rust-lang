//! 量子计算演示示例
//! 
//! 展示如何使用c17_iot的量子计算功能进行量子算法、量子机器学习和量子优化

use c17_iot::quantum_computing::{
    QuantumComputingManager, QuantumConfig, QuantumCircuit,
    QuantumAlgorithmConfig, QuantumAlgorithmType, QuantumGate, QuantumGateOperation
};
use std::time::Duration;
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动量子计算演示...");

    println!("📊 开始演示IoT系统量子计算功能...");

    // 1. 量子计算管理器创建和配置
    println!("\n1️⃣ 量子计算管理器创建和配置");
    demo_quantum_manager_creation().await?;

    // 2. 量子电路创建和执行
    println!("\n2️⃣ 量子电路创建和执行");
    demo_quantum_circuit_operations().await?;

    // 3. 量子算法执行
    println!("\n3️⃣ 量子算法执行");
    demo_quantum_algorithms().await?;

    // 4. 量子机器学习
    println!("\n4️⃣ 量子机器学习");
    demo_quantum_machine_learning().await?;

    // 5. 量子优化
    println!("\n5️⃣ 量子优化");
    demo_quantum_optimization().await?;

    // 6. 量子模拟
    println!("\n6️⃣ 量子模拟");
    demo_quantum_simulation().await?;

    // 7. 量子通信
    println!("\n7️⃣ 量子通信");
    demo_quantum_communication().await?;

    // 8. 量子统计和报告
    println!("\n8️⃣ 量子统计和报告");
    demo_quantum_statistics().await?;

    println!("\n✅ 量子计算演示完成!");
    println!("🎯 演示展示了以下功能:");
    println!("  - 量子电路创建和执行");
    println!("  - 量子算法运行");
    println!("  - 量子机器学习");
    println!("  - 量子优化");
    println!("  - 量子模拟和通信");

    Ok(())
}

/// 量子计算管理器创建和配置演示
async fn demo_quantum_manager_creation() -> Result<(), Box<dyn std::error::Error>> {
    // 创建量子配置
    let config = QuantumConfig {
        enable_quantum: true,
        max_qubits: 20,
        max_circuit_depth: 100,
        default_execution_timeout: Duration::from_secs(300),
        enable_error_correction: true,
        quantum_noise_level: 0.01,
        fidelity_threshold: 0.95,
        custom_params: HashMap::new(),
    };

    println!("  创建量子计算管理器...");
    let quantum_manager = QuantumComputingManager::new(config);
    
    // 获取初始统计信息
    let stats = quantum_manager.get_stats().await;
    println!("  初始量子统计:");
    println!("    总任务数: {}", stats.total_tasks);
    println!("    成功任务数: {}", stats.successful_tasks);
    println!("    失败任务数: {}", stats.failed_tasks);
    println!("    平均执行时间: {:?}", stats.avg_execution_time);
    println!("    总量子比特使用量: {}", stats.total_qubits_used);
    println!("    总量子门使用量: {}", stats.total_gates_used);
    println!("    平均保真度: {:.2}%", stats.avg_fidelity * 100.0);

    Ok(())
}

/// 量子电路创建和执行演示
async fn demo_quantum_circuit_operations() -> Result<(), Box<dyn std::error::Error>> {
    let quantum_manager = QuantumComputingManager::new(QuantumConfig::default());
    
    println!("  创建量子电路...");
    
    // 创建贝尔态电路
    let bell_state_circuit = QuantumCircuit {
        circuit_id: "bell_state_circuit".to_string(),
        circuit_name: "贝尔态电路".to_string(),
        qubit_count: 2,
        gates: vec![
            QuantumGateOperation {
                gate: QuantumGate::Hadamard,
                target_qubits: vec![0],
                control_qubits: vec![],
                parameters: HashMap::new(),
                operation_time: chrono::Utc::now(),
            },
            QuantumGateOperation {
                gate: QuantumGate::CNOT,
                target_qubits: vec![1],
                control_qubits: vec![0],
                parameters: HashMap::new(),
                operation_time: chrono::Utc::now(),
            },
        ],
        depth: 2,
        created_at: chrono::Utc::now(),
        description: "创建贝尔纠缠态 |Φ+⟩ = (|00⟩ + |11⟩)/√2".to_string(),
        expected_result: None,
    };
    
    let circuit_id = quantum_manager.create_quantum_circuit(bell_state_circuit).await?;
    println!("    贝尔态电路已创建: {}", circuit_id);
    
    // 创建量子傅里叶变换电路
    let qft_circuit = QuantumCircuit {
        circuit_id: "qft_circuit".to_string(),
        circuit_name: "量子傅里叶变换电路".to_string(),
        qubit_count: 3,
        gates: vec![
            QuantumGateOperation {
                gate: QuantumGate::Hadamard,
                target_qubits: vec![0],
                control_qubits: vec![],
                parameters: HashMap::new(),
                operation_time: chrono::Utc::now(),
            },
            QuantumGateOperation {
                gate: QuantumGate::Rotation,
                target_qubits: vec![1],
                control_qubits: vec![0],
                parameters: HashMap::from([("angle".to_string(), std::f64::consts::PI / 2.0)]),
                operation_time: chrono::Utc::now(),
            },
            QuantumGateOperation {
                gate: QuantumGate::Hadamard,
                target_qubits: vec![1],
                control_qubits: vec![],
                parameters: HashMap::new(),
                operation_time: chrono::Utc::now(),
            },
            QuantumGateOperation {
                gate: QuantumGate::Rotation,
                target_qubits: vec![2],
                control_qubits: vec![0],
                parameters: HashMap::from([("angle".to_string(), std::f64::consts::PI / 4.0)]),
                operation_time: chrono::Utc::now(),
            },
            QuantumGateOperation {
                gate: QuantumGate::Rotation,
                target_qubits: vec![2],
                control_qubits: vec![1],
                parameters: HashMap::from([("angle".to_string(), std::f64::consts::PI / 2.0)]),
                operation_time: chrono::Utc::now(),
            },
            QuantumGateOperation {
                gate: QuantumGate::Hadamard,
                target_qubits: vec![2],
                control_qubits: vec![],
                parameters: HashMap::new(),
                operation_time: chrono::Utc::now(),
            },
        ],
        depth: 6,
        created_at: chrono::Utc::now(),
        description: "3量子比特量子傅里叶变换".to_string(),
        expected_result: None,
    };
    
    let qft_circuit_id = quantum_manager.create_quantum_circuit(qft_circuit).await?;
    println!("    量子傅里叶变换电路已创建: {}", qft_circuit_id);
    
    println!("  执行量子电路...");
    
    // 执行贝尔态电路
    let bell_result = quantum_manager.execute_quantum_circuit(&circuit_id).await?;
    println!("    贝尔态电路执行结果:");
    println!("      结果ID: {}", bell_result.result_id);
    println!("      期望值: {:.4}", bell_result.expectation_value);
    println!("      方差: {:.4}", bell_result.variance);
    println!("      保真度: {:.4}", bell_result.fidelity);
    println!("      执行时间: {:?}", bell_result.execution_time);
    
    // 执行量子傅里叶变换电路
    let qft_result = quantum_manager.execute_quantum_circuit(&qft_circuit_id).await?;
    println!("    量子傅里叶变换电路执行结果:");
    println!("      结果ID: {}", qft_result.result_id);
    println!("      期望值: {:.4}", qft_result.expectation_value);
    println!("      方差: {:.4}", qft_result.variance);
    println!("      保真度: {:.4}", qft_result.fidelity);
    println!("      执行时间: {:?}", qft_result.execution_time);
    
    // 获取量子电路列表
    let circuits = quantum_manager.get_quantum_circuits().await;
    println!("  已创建的量子电路数量: {}", circuits.len());
    for circuit in circuits {
        println!("    - {}: {} ({} 量子比特, 深度 {})", 
                circuit.circuit_id, 
                circuit.circuit_name, 
                circuit.qubit_count, 
                circuit.depth);
    }

    Ok(())
}

/// 量子算法执行演示
async fn demo_quantum_algorithms() -> Result<(), Box<dyn std::error::Error>> {
    let quantum_manager = QuantumComputingManager::new(QuantumConfig::default());
    
    println!("  执行量子算法...");
    
    // 格罗弗搜索算法
    let grover_config = QuantumAlgorithmConfig {
        algorithm_type: QuantumAlgorithmType::GroverSearch,
        algorithm_name: "格罗弗搜索算法".to_string(),
        qubit_count: 4,
        iterations: 10,
        precision: 0.01,
        max_execution_time: Duration::from_secs(60),
        optimization_params: HashMap::new(),
        custom_params: HashMap::new(),
    };
    
    let grover_input = HashMap::from([
        ("search_space_size".to_string(), "16".to_string()),
        ("target_item".to_string(), "7".to_string()),
        ("oracle_function".to_string(), "f(x) = 1 if x == 7 else 0".to_string()),
    ]);
    
    println!("    执行格罗弗搜索算法...");
    let grover_result = quantum_manager.run_quantum_algorithm(grover_config, grover_input).await?;
    println!("      格罗弗搜索结果:");
    println!("        结果ID: {}", grover_result.result_id);
    println!("        期望值: {:.4}", grover_result.expectation_value);
    println!("        方差: {:.4}", grover_result.variance);
    println!("        保真度: {:.4}", grover_result.fidelity);
    println!("        执行时间: {:?}", grover_result.execution_time);
    
    // 变分量子本征求解器
    let vqe_config = QuantumAlgorithmConfig {
        algorithm_type: QuantumAlgorithmType::VariationalQuantumEigensolver,
        algorithm_name: "变分量子本征求解器".to_string(),
        qubit_count: 6,
        iterations: 100,
        precision: 0.001,
        max_execution_time: Duration::from_secs(300),
        optimization_params: HashMap::from([
            ("learning_rate".to_string(), 0.01),
            ("max_iterations".to_string(), 100.0),
        ]),
        custom_params: HashMap::from([
            ("molecule".to_string(), "H2".to_string()),
            ("basis_set".to_string(), "STO-3G".to_string()),
        ]),
    };
    
    let vqe_input = HashMap::from([
        ("molecule".to_string(), "H2".to_string()),
        ("geometry".to_string(), "H 0.0 0.0 0.0; H 0.0 0.0 0.74".to_string()),
        ("basis_set".to_string(), "STO-3G".to_string()),
    ]);
    
    println!("    执行变分量子本征求解器...");
    let vqe_result = quantum_manager.run_quantum_algorithm(vqe_config, vqe_input).await?;
    println!("      VQE结果:");
    println!("        结果ID: {}", vqe_result.result_id);
    println!("        基态能量: {:.6} Hartree", vqe_result.expectation_value);
    println!("        能量方差: {:.6}", vqe_result.variance);
    println!("        保真度: {:.4}", vqe_result.fidelity);
    println!("        执行时间: {:?}", vqe_result.execution_time);
    
    // 量子近似优化算法
    let qaoa_config = QuantumAlgorithmConfig {
        algorithm_type: QuantumAlgorithmType::QuantumApproximateOptimizationAlgorithm,
        algorithm_name: "量子近似优化算法".to_string(),
        qubit_count: 8,
        iterations: 50,
        precision: 0.01,
        max_execution_time: Duration::from_secs(180),
        optimization_params: HashMap::from([
            ("p_layers".to_string(), 3.0),
            ("optimizer".to_string(), 0.0), // 0: COBYLA, 1: SPSA
        ]),
        custom_params: HashMap::from([
            ("problem_type".to_string(), "MaxCut".to_string()),
            ("graph_size".to_string(), "8".to_string()),
        ]),
    };
    
    let qaoa_input = HashMap::from([
        ("problem_type".to_string(), "MaxCut".to_string()),
        ("graph_edges".to_string(), "[(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]".to_string()),
        ("p_layers".to_string(), "3".to_string()),
    ]);
    
    println!("    执行量子近似优化算法...");
    let qaoa_result = quantum_manager.run_quantum_algorithm(qaoa_config, qaoa_input).await?;
    println!("      QAOA结果:");
    println!("        结果ID: {}", qaoa_result.result_id);
    println!("        优化目标值: {:.4}", qaoa_result.expectation_value);
    println!("        目标方差: {:.4}", qaoa_result.variance);
    println!("        保真度: {:.4}", qaoa_result.fidelity);
    println!("        执行时间: {:?}", qaoa_result.execution_time);

    Ok(())
}

/// 量子机器学习演示
async fn demo_quantum_machine_learning() -> Result<(), Box<dyn std::error::Error>> {
    let quantum_manager = QuantumComputingManager::new(QuantumConfig::default());
    
    println!("  执行量子机器学习...");
    
    // 量子神经网络
    let qnn_config = QuantumAlgorithmConfig {
        algorithm_type: QuantumAlgorithmType::QuantumNeuralNetwork,
        algorithm_name: "量子神经网络".to_string(),
        qubit_count: 4,
        iterations: 200,
        precision: 0.01,
        max_execution_time: Duration::from_secs(600),
        optimization_params: HashMap::from([
            ("learning_rate".to_string(), 0.1),
            ("batch_size".to_string(), 32.0),
            ("epochs".to_string(), 200.0),
        ]),
        custom_params: HashMap::from([
            ("network_type".to_string(), "VariationalQuantumClassifier".to_string()),
            ("feature_map".to_string(), "ZZFeatureMap".to_string()),
        ]),
    };
    
    let qnn_input = HashMap::from([
        ("dataset".to_string(), "iris".to_string()),
        ("feature_dimension".to_string(), "4".to_string()),
        ("num_classes".to_string(), "3".to_string()),
        ("train_size".to_string(), "120".to_string()),
        ("test_size".to_string(), "30".to_string()),
    ]);
    
    println!("    训练量子神经网络...");
    let qnn_result = quantum_manager.run_quantum_algorithm(qnn_config, qnn_input).await?;
    println!("      量子神经网络训练结果:");
    println!("        结果ID: {}", qnn_result.result_id);
    println!("        训练准确率: {:.4}", qnn_result.expectation_value);
    println!("        准确率方差: {:.4}", qnn_result.variance);
    println!("        模型保真度: {:.4}", qnn_result.fidelity);
    println!("        训练时间: {:?}", qnn_result.execution_time);
    
    // 量子支持向量机
    let qsvm_config = QuantumAlgorithmConfig {
        algorithm_type: QuantumAlgorithmType::QuantumSupportVectorMachine,
        algorithm_name: "量子支持向量机".to_string(),
        qubit_count: 6,
        iterations: 100,
        precision: 0.01,
        max_execution_time: Duration::from_secs(300),
        optimization_params: HashMap::from([
            ("C".to_string(), 1.0),
            ("gamma".to_string(), 0.1),
        ]),
        custom_params: HashMap::from([
            ("kernel_type".to_string(), "QuantumKernel".to_string()),
            ("feature_map".to_string(), "PauliFeatureMap".to_string()),
        ]),
    };
    
    let qsvm_input = HashMap::from([
        ("dataset".to_string(), "breast_cancer".to_string()),
        ("feature_dimension".to_string(), "30".to_string()),
        ("num_classes".to_string(), "2".to_string()),
        ("train_size".to_string(), "400".to_string()),
        ("test_size".to_string(), "169".to_string()),
    ]);
    
    println!("    训练量子支持向量机...");
    let qsvm_result = quantum_manager.run_quantum_algorithm(qsvm_config, qsvm_input).await?;
    println!("      量子支持向量机训练结果:");
    println!("        结果ID: {}", qsvm_result.result_id);
    println!("        分类准确率: {:.4}", qsvm_result.expectation_value);
    println!("        准确率方差: {:.4}", qsvm_result.variance);
    println!("        模型保真度: {:.4}", qsvm_result.fidelity);
    println!("        训练时间: {:?}", qsvm_result.execution_time);
    
    // 量子主成分分析
    let qpca_config = QuantumAlgorithmConfig {
        algorithm_type: QuantumAlgorithmType::QuantumPrincipalComponentAnalysis,
        algorithm_name: "量子主成分分析".to_string(),
        qubit_count: 8,
        iterations: 50,
        precision: 0.01,
        max_execution_time: Duration::from_secs(180),
        optimization_params: HashMap::new(),
        custom_params: HashMap::from([
            ("num_components".to_string(), "3".to_string()),
            ("data_dimension".to_string(), "8".to_string()),
        ]),
    };
    
    let qpca_input = HashMap::from([
        ("dataset".to_string(), "synthetic".to_string()),
        ("data_dimension".to_string(), "8".to_string()),
        ("num_samples".to_string(), "1000".to_string()),
        ("num_components".to_string(), "3".to_string()),
    ]);
    
    println!("    执行量子主成分分析...");
    let qpca_result = quantum_manager.run_quantum_algorithm(qpca_config, qpca_input).await?;
    println!("      量子主成分分析结果:");
    println!("        结果ID: {}", qpca_result.result_id);
    println!("        主成分解释方差比: {:.4}", qpca_result.expectation_value);
    println!("        方差比方差: {:.4}", qpca_result.variance);
    println!("        算法保真度: {:.4}", qpca_result.fidelity);
    println!("        执行时间: {:?}", qpca_result.execution_time);

    Ok(())
}

/// 量子优化演示
async fn demo_quantum_optimization() -> Result<(), Box<dyn std::error::Error>> {
    let quantum_manager = QuantumComputingManager::new(QuantumConfig::default());
    
    println!("  执行量子优化...");
    
    // 组合优化问题
    let optimization_config = QuantumAlgorithmConfig {
        algorithm_type: QuantumAlgorithmType::QuantumApproximateOptimizationAlgorithm,
        algorithm_name: "组合优化问题求解".to_string(),
        qubit_count: 10,
        iterations: 100,
        precision: 0.01,
        max_execution_time: Duration::from_secs(300),
        optimization_params: HashMap::from([
            ("p_layers".to_string(), 4.0),
            ("optimizer".to_string(), 0.0),
        ]),
        custom_params: HashMap::from([
            ("problem_type".to_string(), "TravelingSalesman".to_string()),
            ("num_cities".to_string(), "10".to_string()),
        ]),
    };
    
    let optimization_input = HashMap::from([
        ("problem_type".to_string(), "TravelingSalesman".to_string()),
        ("num_cities".to_string(), "10".to_string()),
        ("distance_matrix".to_string(), "random".to_string()),
        ("p_layers".to_string(), "4".to_string()),
    ]);
    
    println!("    求解旅行商问题...");
    let tsp_result = quantum_manager.run_quantum_algorithm(optimization_config, optimization_input).await?;
    println!("      旅行商问题求解结果:");
    println!("        结果ID: {}", tsp_result.result_id);
    println!("        最短路径长度: {:.4}", tsp_result.expectation_value);
    println!("        路径长度方差: {:.4}", tsp_result.variance);
    println!("        优化保真度: {:.4}", tsp_result.fidelity);
    println!("        求解时间: {:?}", tsp_result.execution_time);
    
    // 投资组合优化
    let portfolio_config = QuantumAlgorithmConfig {
        algorithm_type: QuantumAlgorithmType::QuantumApproximateOptimizationAlgorithm,
        algorithm_name: "投资组合优化".to_string(),
        qubit_count: 8,
        iterations: 80,
        precision: 0.01,
        max_execution_time: Duration::from_secs(240),
        optimization_params: HashMap::from([
            ("p_layers".to_string(), 3.0),
            ("risk_tolerance".to_string(), 0.5),
        ]),
        custom_params: HashMap::from([
            ("num_assets".to_string(), "8".to_string()),
            ("optimization_target".to_string(), "SharpeRatio".to_string()),
        ]),
    };
    
    let portfolio_input = HashMap::from([
        ("num_assets".to_string(), "8".to_string()),
        ("expected_returns".to_string(), "random".to_string()),
        ("covariance_matrix".to_string(), "random".to_string()),
        ("risk_tolerance".to_string(), "0.5".to_string()),
    ]);
    
    println!("    执行投资组合优化...");
    let portfolio_result = quantum_manager.run_quantum_algorithm(portfolio_config, portfolio_input).await?;
    println!("      投资组合优化结果:");
    println!("        结果ID: {}", portfolio_result.result_id);
    println!("        夏普比率: {:.4}", portfolio_result.expectation_value);
    println!("        夏普比率方差: {:.4}", portfolio_result.variance);
    println!("        优化保真度: {:.4}", portfolio_result.fidelity);
    println!("        优化时间: {:?}", portfolio_result.execution_time);

    Ok(())
}

/// 量子模拟演示
async fn demo_quantum_simulation() -> Result<(), Box<dyn std::error::Error>> {
    let quantum_manager = QuantumComputingManager::new(QuantumConfig::default());
    
    println!("  执行量子模拟...");
    
    // 量子化学模拟
    let chemistry_config = QuantumAlgorithmConfig {
        algorithm_type: QuantumAlgorithmType::VariationalQuantumEigensolver,
        algorithm_name: "量子化学模拟".to_string(),
        qubit_count: 12,
        iterations: 200,
        precision: 0.001,
        max_execution_time: Duration::from_secs(600),
        optimization_params: HashMap::from([
            ("learning_rate".to_string(), 0.01),
            ("max_iterations".to_string(), 200.0),
        ]),
        custom_params: HashMap::from([
            ("molecule".to_string(), "LiH".to_string()),
            ("basis_set".to_string(), "6-31G".to_string()),
            ("geometry".to_string(), "Li 0.0 0.0 0.0; H 0.0 0.0 1.6".to_string()),
        ]),
    };
    
    let chemistry_input = HashMap::from([
        ("molecule".to_string(), "LiH".to_string()),
        ("geometry".to_string(), "Li 0.0 0.0 0.0; H 0.0 0.0 1.6".to_string()),
        ("basis_set".to_string(), "6-31G".to_string()),
        ("charge".to_string(), "0".to_string()),
        ("multiplicity".to_string(), "1".to_string()),
    ]);
    
    println!("    执行LiH分子量子化学模拟...");
    let chemistry_result = quantum_manager.run_quantum_algorithm(chemistry_config, chemistry_input).await?;
    println!("      量子化学模拟结果:");
    println!("        结果ID: {}", chemistry_result.result_id);
    println!("        基态能量: {:.6} Hartree", chemistry_result.expectation_value);
    println!("        能量方差: {:.6}", chemistry_result.variance);
    println!("        模拟保真度: {:.4}", chemistry_result.fidelity);
    println!("        模拟时间: {:?}", chemistry_result.execution_time);
    
    // 量子材料模拟
    let material_config = QuantumAlgorithmConfig {
        algorithm_type: QuantumAlgorithmType::VariationalQuantumEigensolver,
        algorithm_name: "量子材料模拟".to_string(),
        qubit_count: 16,
        iterations: 150,
        precision: 0.001,
        max_execution_time: Duration::from_secs(900),
        optimization_params: HashMap::from([
            ("learning_rate".to_string(), 0.005),
            ("max_iterations".to_string(), 150.0),
        ]),
        custom_params: HashMap::from([
            ("material".to_string(), "Graphene".to_string()),
            ("lattice_size".to_string(), "4x4".to_string()),
            ("interaction_type".to_string(), "Hubbard".to_string()),
        ]),
    };
    
    let material_input = HashMap::from([
        ("material".to_string(), "Graphene".to_string()),
        ("lattice_size".to_string(), "4x4".to_string()),
        ("interaction_type".to_string(), "Hubbard".to_string()),
        ("U_parameter".to_string(), "2.0".to_string()),
        ("t_parameter".to_string(), "1.0".to_string()),
    ]);
    
    println!("    执行石墨烯量子材料模拟...");
    let material_result = quantum_manager.run_quantum_algorithm(material_config, material_input).await?;
    println!("      量子材料模拟结果:");
    println!("        结果ID: {}", material_result.result_id);
    println!("        基态能量: {:.6} eV", material_result.expectation_value);
    println!("        能量方差: {:.6}", material_result.variance);
    println!("        模拟保真度: {:.4}", material_result.fidelity);
    println!("        模拟时间: {:?}", material_result.execution_time);

    Ok(())
}

/// 量子通信演示
async fn demo_quantum_communication() -> Result<(), Box<dyn std::error::Error>> {
    let quantum_manager = QuantumComputingManager::new(QuantumConfig::default());
    
    println!("  执行量子通信...");
    
    // 量子密钥分发
    let qkd_config = QuantumAlgorithmConfig {
        algorithm_type: QuantumAlgorithmType::QuantumCommunication,
        algorithm_name: "量子密钥分发".to_string(),
        qubit_count: 4,
        iterations: 1000,
        precision: 0.01,
        max_execution_time: Duration::from_secs(120),
        optimization_params: HashMap::new(),
        custom_params: HashMap::from([
            ("protocol".to_string(), "BB84".to_string()),
            ("key_length".to_string(), "256".to_string()),
        ]),
    };
    
    let qkd_input = HashMap::from([
        ("protocol".to_string(), "BB84".to_string()),
        ("key_length".to_string(), "256".to_string()),
        ("channel_noise".to_string(), "0.01".to_string()),
        ("eavesdropper".to_string(), "false".to_string()),
    ]);
    
    println!("    执行BB84量子密钥分发协议...");
    let qkd_result = quantum_manager.run_quantum_algorithm(qkd_config, qkd_input).await?;
    println!("      量子密钥分发结果:");
    println!("        结果ID: {}", qkd_result.result_id);
    println!("        密钥生成成功率: {:.4}", qkd_result.expectation_value);
    println!("        成功率方差: {:.4}", qkd_result.variance);
    println!("        通信保真度: {:.4}", qkd_result.fidelity);
    println!("        密钥分发时间: {:?}", qkd_result.execution_time);
    
    // 量子隐形传态
    let teleportation_config = QuantumAlgorithmConfig {
        algorithm_type: QuantumAlgorithmType::QuantumCommunication,
        algorithm_name: "量子隐形传态".to_string(),
        qubit_count: 3,
        iterations: 100,
        precision: 0.01,
        max_execution_time: Duration::from_secs(60),
        optimization_params: HashMap::new(),
        custom_params: HashMap::from([
            ("protocol".to_string(), "QuantumTeleportation".to_string()),
            ("state_to_teleport".to_string(), "|ψ⟩ = α|0⟩ + β|1⟩".to_string()),
        ]),
    };
    
    let teleportation_input = HashMap::from([
        ("protocol".to_string(), "QuantumTeleportation".to_string()),
        ("state_to_teleport".to_string(), "|ψ⟩ = α|0⟩ + β|1⟩".to_string()),
        ("channel_noise".to_string(), "0.005".to_string()),
        ("measurement_basis".to_string(), "Bell".to_string()),
    ]);
    
    println!("    执行量子隐形传态协议...");
    let teleportation_result = quantum_manager.run_quantum_algorithm(teleportation_config, teleportation_input).await?;
    println!("      量子隐形传态结果:");
    println!("        结果ID: {}", teleportation_result.result_id);
    println!("        传态保真度: {:.4}", teleportation_result.expectation_value);
    println!("        保真度方差: {:.4}", teleportation_result.variance);
    println!("        协议保真度: {:.4}", teleportation_result.fidelity);
    println!("        传态时间: {:?}", teleportation_result.execution_time);

    Ok(())
}

/// 量子统计和报告演示
async fn demo_quantum_statistics() -> Result<(), Box<dyn std::error::Error>> {
    let quantum_manager = QuantumComputingManager::new(QuantumConfig::default());
    
    println!("  生成量子统计报告...");
    
    // 执行一些操作以生成统计数据
    // 创建并执行量子电路
    let test_circuit = QuantumCircuit {
        circuit_id: "stats_test_circuit".to_string(),
        circuit_name: "统计测试电路".to_string(),
        qubit_count: 2,
        gates: vec![
            QuantumGateOperation {
                gate: QuantumGate::Hadamard,
                target_qubits: vec![0],
                control_qubits: vec![],
                parameters: HashMap::new(),
                operation_time: chrono::Utc::now(),
            },
        ],
        depth: 1,
        created_at: chrono::Utc::now(),
        description: "用于统计测试的简单电路".to_string(),
        expected_result: None,
    };
    
    quantum_manager.create_quantum_circuit(test_circuit).await?;
    quantum_manager.execute_quantum_circuit("stats_test_circuit").await?;
    
    // 执行一些量子算法
    for i in 0..3 {
        let algorithm_config = QuantumAlgorithmConfig {
            algorithm_type: QuantumAlgorithmType::GroverSearch,
            algorithm_name: format!("测试算法 {}", i),
            qubit_count: 3,
            iterations: 10,
            precision: 0.01,
            max_execution_time: Duration::from_secs(30),
            optimization_params: HashMap::new(),
            custom_params: HashMap::new(),
        };
        
        let input_data = HashMap::from([
            ("test_param".to_string(), i.to_string()),
        ]);
        
        let _ = quantum_manager.run_quantum_algorithm(algorithm_config, input_data).await?;
    }
    
    // 获取统计信息
    let stats = quantum_manager.get_stats().await;
    println!("  量子统计报告:");
    println!("    总任务数: {}", stats.total_tasks);
    println!("    成功任务数: {}", stats.successful_tasks);
    println!("    失败任务数: {}", stats.failed_tasks);
    println!("    平均执行时间: {:?}", stats.avg_execution_time);
    println!("    总量子比特使用量: {}", stats.total_qubits_used);
    println!("    总量子门使用量: {}", stats.total_gates_used);
    println!("    平均保真度: {:.2}%", stats.avg_fidelity * 100.0);
    println!("    最后更新时间: {}", stats.last_updated.format("%Y-%m-%d %H:%M:%S"));
    
    println!("    算法使用统计:");
    for (algorithm_name, usage_count) in &stats.algorithm_usage {
        println!("      {}: {} 次", algorithm_name, usage_count);
    }
    
    // 获取量子电路列表
    let circuits = quantum_manager.get_quantum_circuits().await;
    println!("  量子电路列表 ({} 个):", circuits.len());
    for circuit in circuits {
        println!("    - {}: {} ({} 量子比特, 深度 {})", 
                circuit.circuit_id, 
                circuit.circuit_name, 
                circuit.qubit_count, 
                circuit.depth);
    }
    
    // 获取量子任务列表
    let tasks = quantum_manager.get_quantum_tasks(Some(5)).await;
    println!("  最近量子任务 ({} 个):", tasks.len());
    for (i, task) in tasks.iter().enumerate() {
        println!("    {}: {:?} - {:?} ({} 量子比特)", 
                i + 1, 
                task.task_type, 
                task.status, 
                task.quantum_resources.qubits_used);
        if let Some(execution_time) = task.execution_time {
            println!("      执行时间: {:?}", execution_time);
        }
    }

    Ok(())
}
