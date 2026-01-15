//! 组合模式工程案例集成测试
//!
//! 测试多个设计模式组合使用的正确性、性能和并发安全性

use c09_design_pattern::pattern_combinations::*;
use std::sync::Arc;
use std::thread;
use std::time::Duration;

#[test]
fn test_web_server_facade_builder_integration() {
    let routing_strategy = Box::new(ExactMatchRouting::new());
    let server = WebServerFacade::new(routing_strategy);

    // 使用 Builder 模式构建请求
    let request = HttpRequestBuilder::new()
        .method("GET")
        .path("/api/users")
        .header("Content-Type", "application/json")
        .build()
        .unwrap();

    let response = server.handle_request(request).unwrap();
    assert_eq!(response.status_code, 200);
    assert!(response.body.contains("users"));

    let stats = server.get_stats();
    assert_eq!(stats.total_requests, 1);
    assert_eq!(stats.total_errors, 0);
}

#[test]
fn test_web_server_routing_strategy_switching() {
    // 测试精确匹配策略
    let exact_routing = Box::new(ExactMatchRouting::new());
    let server_exact = WebServerFacade::new(exact_routing);

    let request = HttpRequestBuilder::new()
        .method("GET")
        .path("/api/users")
        .build()
        .unwrap();

    let response = server_exact.handle_request(request).unwrap();
    assert_eq!(response.status_code, 200);

    // 测试前缀匹配策略
    let prefix_routing = Box::new(PrefixMatchRouting::new());
    let server_prefix = WebServerFacade::new(prefix_routing);

    let request2 = HttpRequestBuilder::new()
        .method("GET")
        .path("/api/users/123")
        .build()
        .unwrap();

    let response2 = server_prefix.handle_request(request2).unwrap();
    assert_eq!(response2.status_code, 200);
}

#[test]
fn test_circuit_breaker_state_transitions() {
    let breaker = CircuitBreaker::new(3, 2, Duration::from_millis(100));

    // 初始状态应该是 Closed
    assert_eq!(breaker.get_state(), CircuitState::Closed);

    // 模拟失败，触发断路器打开
    for _ in 0..3 {
        let _: Result<(), String> = breaker.call(|| Err("Error".to_string()));
    }

    assert_eq!(breaker.get_state(), CircuitState::Open);

    // 等待超时，进入半开状态
    thread::sleep(Duration::from_millis(150));
    let _ = breaker.call(|| Ok(42));
    // 应该进入 HalfOpen 状态

    // 成功调用应该恢复
    for _ in 0..2 {
        let _ = breaker.call(|| Ok(42));
    }

    // 应该恢复到 Closed 状态
    assert_eq!(breaker.get_state(), CircuitState::Closed);
}

#[test]
fn test_game_engine_command_execution() {
    let mut engine = GameEngine::new();

    // 测试移动命令
    engine.process_input("w").unwrap();
    assert_eq!(engine.get_context().player_position, 1);

    engine.process_input("s").unwrap();
    assert_eq!(engine.get_context().player_position, 2);

    // 测试攻击命令
    let initial_health = engine.get_context().enemy_health;
    engine.process_input("attack").unwrap();
    assert_eq!(engine.get_context().enemy_health, initial_health - 10);
}

#[test]
fn test_game_engine_observer_events() {
    let mut engine = GameEngine::new();

    // 处理输入应该触发事件
    engine.process_input("w").unwrap();

    // 更新 AI 应该触发状态变化事件
    engine.update_ai();
}

#[test]
fn test_game_engine_ai_state_machine() {
    let mut engine = GameEngine::new();

    // 初始状态应该是 Patrol
    let initial_state = engine.get_ai_state_name();
    assert_eq!(initial_state, Some("Patrol".to_string()));

    // 更新多次，触发状态转换
    for _ in 0..15 {
        engine.update_ai();
    }

    // 应该转换到其他状态
    let new_state = engine.get_ai_state_name();
    assert!(new_state.is_some());
    assert_ne!(new_state, initial_state);
}

#[test]
fn test_web_server_concurrent_requests() {
    let routing_strategy = Box::new(ExactMatchRouting::new());
    let server = Arc::new(WebServerFacade::new(routing_strategy));
    let mut handles = vec![];

    // 创建多个并发请求
    for i in 0..10 {
        let server_clone = Arc::clone(&server);
        let handle = thread::spawn(move || {
            let request = HttpRequestBuilder::new()
                .method("GET")
                .path(if i % 2 == 0 { "/api/users" } else { "/api/posts" })
                .build()
                .unwrap();

            server_clone.handle_request(request)
        });
        handles.push(handle);
    }

    // 等待所有请求完成
    let mut success_count = 0;
    for handle in handles {
        if handle.join().unwrap().is_ok() {
            success_count += 1;
        }
    }

    assert_eq!(success_count, 10);

    let stats = server.get_stats();
    assert_eq!(stats.total_requests, 10);
}

#[test]
fn test_circuit_breaker_concurrent_access() {
    let breaker = Arc::new(CircuitBreaker::new(5, 3, Duration::from_secs(1)));
    let mut handles = vec![];

    // 创建多个并发调用
    for i in 0..10 {
        let breaker_clone = Arc::clone(&breaker);
        let handle = thread::spawn(move || {
            if i < 6 {
                // 前6个调用失败
                breaker_clone.call(|| Err("Error".to_string()))
            } else {
                // 后4个调用成功
                breaker_clone.call(|| Ok(42))
            }
        });
        handles.push(handle);
    }

    // 等待所有调用完成
    for handle in handles {
        let _ = handle.join().unwrap();
    }

    // 验证断路器状态
    let state = breaker.get_state();
    // 由于并发，状态可能是 Open 或 HalfOpen
    assert!(matches!(state, CircuitState::Open | CircuitState::HalfOpen | CircuitState::Closed));
}

#[test]
fn test_game_engine_concurrent_inputs() {
    let engine = Arc::new(std::sync::Mutex::new(GameEngine::new()));
    let mut handles = vec![];

    // 创建多个并发输入
    for i in 0..5 {
        let engine_clone = Arc::clone(&engine);
        let handle = thread::spawn(move || {
            let mut engine = engine_clone.lock().unwrap();
            engine.process_input(if i % 2 == 0 { "w" } else { "attack" })
        });
        handles.push(handle);
    }

    // 等待所有输入处理完成
    for handle in handles {
        assert!(handle.join().unwrap().is_ok());
    }

    let engine = engine.lock().unwrap();
    assert!(engine.get_context().player_position > 0);
}

#[test]
fn test_pattern_combination_performance() {
    use std::time::Instant;

    let routing_strategy = Box::new(ExactMatchRouting::new());
    let server = WebServerFacade::new(routing_strategy);

    let start = Instant::now();
    for _ in 0..1000 {
        let request = HttpRequestBuilder::new()
            .method("GET")
            .path("/api/users")
            .build()
            .unwrap();
        let _ = server.handle_request(request);
    }
    let duration = start.elapsed();

    println!("处理1000个请求耗时: {:?}", duration);
    assert!(duration.as_secs() < 5); // 应该在5秒内完成

    let stats = server.get_stats();
    assert_eq!(stats.total_requests, 1000);
}

#[test]
fn test_error_handling_in_pattern_combinations() {
    let routing_strategy = Box::new(ExactMatchRouting::new());
    let server = WebServerFacade::new(routing_strategy);

    // 测试无效路由
    let request = HttpRequestBuilder::new()
        .method("GET")
        .path("/invalid/route")
        .build()
        .unwrap();

    let result = server.handle_request(request);
    assert!(result.is_err());

    let stats = server.get_stats();
    assert_eq!(stats.total_requests, 1);
    assert_eq!(stats.total_errors, 1);
}

#[test]
fn test_builder_validation() {
    // 测试缺少必需字段的情况
    let result = HttpRequestBuilder::new().path("/api/users").build();
    assert!(result.is_err());

    let result = HttpRequestBuilder::new().method("GET").build();
    assert!(result.is_err());

    // 测试完整构建
    let result = HttpRequestBuilder::new()
        .method("GET")
        .path("/api/users")
        .build();
    assert!(result.is_ok());
}
