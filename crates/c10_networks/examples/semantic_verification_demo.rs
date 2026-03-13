//! 语义验证演示示例
//!
//! 本示例展示了如何使用C10 Networks的语义验证框架来验证网络协议的正确性。
use c10_networks::semantics::formal_spec::{
    HttpFormalSpec, HttpMethod, HttpRuleAction, HttpStatusCode, HttpVersion, TcpEvent,
    TcpFormalSpec,
};
use c10_networks::semantics::model_checking::{
    ModelChecker, ModelCheckingConfig, TlaConfig, TlaModelChecker,
};
use c10_networks::semantics::*;
use std::collections::HashMap;

/// 演示TCP协议语义验证
async fn demo_tcp_semantic_verification() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== TCP协议语义验证演示 ===");

    // 创建TCP形式化规范
    let tcp_spec = TcpFormalSpec::new();
    println!(
        "TCP规范创建完成，包含 {} 个状态和 {} 个转换",
        tcp_spec.states.len(),
        tcp_spec.get_transition_table().len()
    );

    // 创建TCP连接状态
    let mut tcp_connection = ConnectionState {
        connection_id: "demo_conn_1".to_string(),
        state: TcpState::Closed,
        sequence_number: 0,
        acknowledgment_number: 0,
        window_size: 1024,
        message_history: Vec::new(),
        authenticated: false,
        encrypted: false,
    };

    println!("\n初始连接状态: {:?}", tcp_connection.state);

    // 模拟TCP三次握手
    println!("\n--- 开始TCP三次握手 ---");

    // 1. 主动打开 -> SYN_SENT
    tcp_connection.state = TcpState::SynSent;
    tcp_connection.sequence_number = 1000;
    println!(
        "1. 主动打开: {:?}, 序列号: {}",
        tcp_connection.state, tcp_connection.sequence_number
    );

    // 2. 接收SYN+ACK -> SYN_RECEIVED
    if let Some(new_state) = tcp_spec.get_transition(tcp_connection.state, TcpEvent::ReceiveSynAck)
    {
        tcp_connection.state = new_state;
        tcp_connection.acknowledgment_number = 2001; // 假设对端序列号2000
        println!(
            "2. 接收SYN+ACK: {:?}, 确认号: {}",
            tcp_connection.state, tcp_connection.acknowledgment_number
        );
    }

    // 3. 发送ACK -> ESTABLISHED
    if let Some(new_state) = tcp_spec.get_transition(tcp_connection.state, TcpEvent::SendAck) {
        tcp_connection.state = new_state;
        tcp_connection.authenticated = true;
        tcp_connection.encrypted = true;
        println!("3. 发送ACK: {:?}, 连接建立完成", tcp_connection.state);
    }

    // 验证不变量
    println!("\n--- 验证TCP不变量 ---");
    for invariant in tcp_spec.get_invariants() {
        let is_satisfied = tcp_spec.check_invariant(&tcp_connection, invariant);
        println!(
            "不变量 '{}': {}",
            invariant.name,
            if is_satisfied { "满足" } else { "违反" }
        );
    }

    // 模拟连接关闭
    println!("\n--- 开始连接关闭 ---");

    // 发送FIN -> FIN_WAIT_1
    if let Some(new_state) = tcp_spec.get_transition(tcp_connection.state, TcpEvent::SendFin) {
        tcp_connection.state = new_state;
        println!("4. 发送FIN: {:?}", tcp_connection.state);
    }

    // 接收ACK -> FIN_WAIT_2
    if let Some(new_state) = tcp_spec.get_transition(tcp_connection.state, TcpEvent::ReceiveAck) {
        tcp_connection.state = new_state;
        println!("5. 接收ACK: {:?}", tcp_connection.state);
    }

    // 接收FIN -> TIME_WAIT
    if let Some(new_state) = tcp_spec.get_transition(tcp_connection.state, TcpEvent::ReceiveFin) {
        tcp_connection.state = new_state;
        println!("6. 接收FIN: {:?}", tcp_connection.state);
    }

    // 超时 -> CLOSED
    if let Some(new_state) = tcp_spec.get_transition(tcp_connection.state, TcpEvent::Timeout) {
        tcp_connection.state = new_state;
        println!("7. 超时: {:?}, 连接关闭完成", tcp_connection.state);
    }

    Ok(())
}

/// 演示HTTP协议语义验证
async fn demo_http_semantic_verification() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== HTTP协议语义验证演示 ===");

    // 创建HTTP形式化规范
    let http_spec = HttpFormalSpec::new(HttpVersion::Http1_1);
    println!(
        "HTTP/1.1规范创建完成，支持 {} 个方法和 {} 个状态码",
        http_spec.methods.len(),
        http_spec.status_codes.len()
    );

    // 创建HTTP请求头部
    let mut request_headers = HashMap::new();
    request_headers.insert("Host".to_string(), "example.com".to_string());
    request_headers.insert("Content-Type".to_string(), "application/json".to_string());
    request_headers.insert("Authorization".to_string(), "Bearer token123".to_string());

    // 验证GET请求
    println!("\n--- 验证GET请求 ---");
    let get_valid = http_spec.is_valid_request(&HttpMethod::Get, &request_headers);
    println!("GET请求有效性: {}", if get_valid { "有效" } else { "无效" });

    // 验证POST请求
    println!("\n--- 验证POST请求 ---");
    let post_valid = http_spec.is_valid_request(&HttpMethod::Post, &request_headers);
    println!(
        "POST请求有效性: {}",
        if post_valid { "有效" } else { "无效" }
    );

    // 应用协议规则
    println!("\n--- 应用协议规则 ---");
    let rules = http_spec.apply_rules(&HttpMethod::Post, &request_headers);
    println!("应用了 {} 个协议规则", rules.len());

    for rule in rules {
        match rule {
            HttpRuleAction::Allow => println!("  规则: 允许请求"),
            HttpRuleAction::Deny => println!("  规则: 拒绝请求"),
            HttpRuleAction::ModifyHeader { name, value } => {
                println!("  规则: 修改头部 {} = {}", name, value);
            }
            HttpRuleAction::Cache { duration } => {
                println!("  规则: 缓存 {} 秒", duration);
            }
            HttpRuleAction::Redirect { location } => {
                println!("  规则: 重定向到 {}", location);
            }
        }
    }

    // 创建HTTP响应头部
    let mut response_headers = HashMap::new();
    response_headers.insert("Content-Type".to_string(), "application/json".to_string());
    response_headers.insert("Content-Length".to_string(), "1024".to_string());
    response_headers.insert("Server".to_string(), "C10-Networks/1.0".to_string());

    // 验证HTTP响应
    println!("\n--- 验证HTTP响应 ---");
    let success_response = HttpStatusCode::Success(200);
    let success_valid = http_spec.is_valid_response(&success_response, &response_headers);
    println!(
        "200响应有效性: {}",
        if success_valid { "有效" } else { "无效" }
    );

    let not_found_response = HttpStatusCode::ClientError(404);
    let not_found_valid = http_spec.is_valid_response(&not_found_response, &response_headers);
    println!(
        "404响应有效性: {}",
        if not_found_valid { "有效" } else { "无效" }
    );

    Ok(())
}

/// 演示模型检查
async fn demo_model_checking() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 模型检查演示 ===");

    // 创建模型检查配置
    let config = ModelCheckingConfig {
        max_states: 1000,
        timeout: std::time::Duration::from_secs(30),
        parallel_exploration: true,
        state_compression: true,
        verbose: true,
    };

    // 创建模型检查器
    let mut model_checker = ModelChecker::new(config);

    // 添加状态转换
    let transition1 = StateTransition {
        id: "transition_1".to_string(),
        from: "initial".to_string(),
        to: "connected".to_string(),
        guard: Guard::True,
        action: Action::Assignment {
            variable: "state".to_string(),
            value: Value::String("connected".to_string()),
        },
    };

    let transition2 = StateTransition {
        id: "transition_2".to_string(),
        from: "connected".to_string(),
        to: "disconnected".to_string(),
        guard: Guard::True,
        action: Action::Assignment {
            variable: "state".to_string(),
            value: Value::String("disconnected".to_string()),
        },
    };

    model_checker.add_transition(transition1);
    model_checker.add_transition(transition2);

    // 创建初始状态
    let mut initial_vars = HashMap::new();
    initial_vars.insert("state".to_string(), Value::String("initial".to_string()));
    initial_vars.insert("connection_count".to_string(), Value::Int(0));

    let initial_state = NetworkState {
        id: "initial".to_string(),
        connections: HashMap::new(),
        message_queue: Vec::new(),
        global_vars: initial_vars,
        timestamp: 0,
    };

    println!("开始模型检查...");

    // 执行模型检查
    let result = model_checker.check_model(initial_state)?;

    println!("模型检查完成:");
    println!("  成功: {}", result.success);
    println!("  探索状态数: {}", result.states_explored);
    println!("  发现违规: {}", result.violations.len());
    println!("  检查时间: {:?}", result.checking_time);
    println!("  内存使用: {} bytes", result.memory_usage);
    println!(
        "  状态覆盖度: {:.2}%",
        result.coverage.state_coverage * 100.0
    );

    // 显示发现的违规
    if !result.violations.is_empty() {
        println!("\n发现的违规:");
        for violation in &result.violations {
            println!(
                "  - {}: {}",
                violation.violation_type.clone() as u8,
                violation.description
            );
        }
    }

    // 显示反例
    if !result.counter_examples.is_empty() {
        println!("\n反例:");
        for counter_example in &result.counter_examples {
            println!(
                "  - {}: {}",
                counter_example.id, counter_example.description
            );
            println!("    违规属性: {}", counter_example.violated_property);
            println!("    执行路径长度: {}", counter_example.execution_path.len());
        }
    }

    Ok(())
}

/// 演示TLA+模型检查
async fn demo_tla_model_checking() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== TLA+模型检查演示 ===");

    // 创建语义模型
    let mut state_vars = HashMap::new();
    state_vars.insert("connections".to_string(), Value::Int(0));
    state_vars.insert("messages".to_string(), Value::Int(0));

    let initial_state = NetworkState {
        id: "initial".to_string(),
        connections: HashMap::new(),
        message_queue: Vec::new(),
        global_vars: state_vars,
        timestamp: 0,
    };

    let model = SemanticModel {
        name: "network_protocol_model".to_string(),
        state_variables: initial_state.global_vars.clone(),
        transitions: Vec::new(),
        invariants: Vec::new(),
        initial_state: initial_state.clone(),
    };

    // 创建TLA+模型检查器
    let tla_config = TlaConfig::default();
    let tla_checker = TlaModelChecker::new(String::new(), tla_config);

    // 生成TLA+规范
    let tla_spec = tla_checker.generate_spec(&model);
    println!("生成的TLA+规范:");
    println!("{}", tla_spec);

    // 执行TLA+检查
    println!("\n执行TLA+模型检查...");
    let tla_result = tla_checker.check_spec()?;

    println!("TLA+检查结果:");
    println!("  成功: {}", tla_result.success);
    println!("  探索状态数: {}", tla_result.states_explored);
    println!("  检查时间: {:?}", tla_result.checking_time);
    println!(
        "  状态覆盖度: {:.2}%",
        tla_result.coverage.state_coverage * 100.0
    );

    Ok(())
}

/// 演示属性检查器
async fn demo_property_checker() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== 属性检查器演示 ===");

    // 创建网络状态
    let mut connections = HashMap::new();
    connections.insert(
        "conn_1".to_string(),
        ConnectionState {
            connection_id: "conn_1".to_string(),
            state: TcpState::Established,
            sequence_number: 1000,
            acknowledgment_number: 500,
            window_size: 1024,
            message_history: Vec::new(),
            authenticated: true,
            encrypted: true,
        },
    );

    let network_state = NetworkState {
        id: "demo_state".to_string(),
        connections,
        message_queue: Vec::new(),
        global_vars: HashMap::new(),
        timestamp: 12345,
    };

    // 创建语义验证器
    let config = VerificationConfig::default();
    let verifier = SemanticVerifier::new(config);

    // 验证网络状态
    let violations = verifier.verify_state(&network_state);

    println!("网络状态验证结果:");
    println!("  状态ID: {}", network_state.id);
    println!("  连接数: {}", network_state.connections.len());
    println!("  消息队列大小: {}", network_state.message_queue.len());
    println!("  发现的违规: {}", violations.len());

    // 显示连接状态
    for (conn_id, conn_state) in &network_state.connections {
        println!(
            "  连接 {}: {:?}, 认证: {}, 加密: {}",
            conn_id, conn_state.state, conn_state.authenticated, conn_state.encrypted
        );
    }

    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 C10 Networks 语义验证演示");
    println!("================================");

    // 演示TCP协议语义验证
    demo_tcp_semantic_verification().await?;

    // 演示HTTP协议语义验证
    demo_http_semantic_verification().await?;

    // 演示模型检查
    demo_model_checking().await?;

    // 演示TLA+模型检查
    demo_tla_model_checking().await?;

    // 演示属性检查器
    demo_property_checker().await?;

    println!("\n✅ 所有语义验证演示完成！");

    Ok(())
}
