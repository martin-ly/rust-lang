//! Rust 1.94 ControlFlow 完整示例
//! 
//! ControlFlow<B, C> 用于在迭代器中实现提前终止控制

#![allow(dead_code)]

use std::ops::ControlFlow;

// =============================================================================
// 基础示例
// =============================================================================

/// 在迭代中查找第一个满足条件的元素
fn find_first<T>(items: &[T], predicate: impl Fn(&T) -> bool) -> Option<&T> {
    items.iter().try_for_each(|item| {
        if predicate(item) {
            ControlFlow::Break(item)
        } else {
            ControlFlow::Continue(())
        }
    }).break_value()
}

/// 验证所有元素
fn validate_all<T>(items: &[T], validator: impl Fn(&T) -> bool) -> bool {
    matches!(
        items.iter().try_for_each(|item| {
            if validator(item) {
                ControlFlow::Continue(())
            } else {
                ControlFlow::Break(())
            }
        }),
        ControlFlow::Continue(_)
    )
}

// =============================================================================
// 验证管道示例
// =============================================================================

#[derive(Debug)]
struct UserRegistration {
    username: String,
    email: String,
    password: String,
    age: u32,
}

#[derive(Debug)]
enum ValidationError {
    InvalidUsername(String),
    InvalidEmail(String),
    WeakPassword(String),
    UnderAge(u32),
}

/// 使用 ControlFlow 构建验证管道
fn validate_registration(data: &UserRegistration) -> ControlFlow<ValidationError, ()> {
    // 验证用户名
    if data.username.len() < 3 {
        return ControlFlow::Break(ValidationError::InvalidUsername(
            "用户名至少3个字符".to_string()
        ));
    }
    
    // 验证邮箱格式
    if !data.email.contains('@') || !data.email.contains('.') {
        return ControlFlow::Break(ValidationError::InvalidEmail(
            "邮箱格式不正确".to_string()
        ));
    }
    
    // 验证密码强度
    if data.password.len() < 8 {
        return ControlFlow::Break(ValidationError::WeakPassword(
            "密码至少8个字符".to_string()
        ));
    }
    
    if !data.password.chars().any(|c| c.is_ascii_digit()) {
        return ControlFlow::Break(ValidationError::WeakPassword(
            "密码必须包含数字".to_string()
        ));
    }
    
    if !data.password.chars().any(|c| c.is_ascii_uppercase()) {
        return ControlFlow::Break(ValidationError::WeakPassword(
            "密码必须包含大写字母".to_string()
        ));
    }
    
    // 验证年龄
    if data.age < 18 {
        return ControlFlow::Break(ValidationError::UnderAge(data.age));
    }
    
    ControlFlow::Continue(())
}

/// 执行注册
fn register_user(data: UserRegistration) -> Result<String, ValidationError> {
    match validate_registration(&data) {
        ControlFlow::Continue(_) => {
            println!("用户注册成功: {}", data.username);
            Ok(format!("user_id_{}", data.username))
        }
        ControlFlow::Break(err) => {
            println!("验证失败: {:?}", err);
            Err(err)
        }
    }
}

// =============================================================================
// 数据处理管道
// =============================================================================

#[derive(Debug)]
struct DataItem {
    id: u32,
    value: f64,
    category: String,
}

#[derive(Debug)]
enum ProcessingError {
    InvalidValue(u32, f64),
    MissingCategory(u32),
    ThresholdExceeded(u32, f64),
}

/// 数据处理管道
fn process_data_pipeline(
    items: &[DataItem],
    threshold: f64
) -> ControlFlow<ProcessingError, Vec<f64>> {
    let mut results = Vec::new();
    
    for item in items {
        // 步骤1: 验证值
        if item.value.is_nan() || item.value.is_infinite() {
            return ControlFlow::Break(ProcessingError::InvalidValue(
                item.id, item.value
            ));
        }
        
        // 步骤2: 验证类别
        if item.category.is_empty() {
            return ControlFlow::Break(ProcessingError::MissingCategory(item.id));
        }
        
        // 步骤3: 阈值检查
        if item.value > threshold {
            return ControlFlow::Break(ProcessingError::ThresholdExceeded(
                item.id, item.value
            ));
        }
        
        // 处理数据
        let processed = item.value * 2.0;
        results.push(processed);
    }
    
    ControlFlow::Continue(results)
}

// =============================================================================
// 迭代器短路优化
// =============================================================================

/// 使用 try_fold 进行提前终止
fn sum_until_limit(numbers: &[i32], limit: i32) -> ControlFlow<i32, i32> {
    numbers.iter().try_fold(0, |acc, &n| {
        let new_sum = acc + n;
        if new_sum > limit {
            ControlFlow::Break(new_sum)
        } else {
            ControlFlow::Continue(new_sum)
        }
    })
}

/// 查找并转换
fn find_and_transform<T, U>(
    items: &[T],
    predicate: impl Fn(&T) -> bool,
    transform: impl Fn(&T) -> U,
) -> Option<U> {
    items.iter().try_for_each(|item| {
        if predicate(item) {
            ControlFlow::Break(transform(item))
        } else {
            ControlFlow::Continue(())
        }
    }).break_value()
}

// =============================================================================
// 状态机实现
// =============================================================================

#[derive(Debug, Clone)]
enum State {
    Idle,
    Processing(u32),
    Completed(String),
    Failed(String),
}

#[derive(Debug)]
enum StateError {
    InvalidTransition(String, String),
    MaxRetriesExceeded,
}

/// 状态转换
fn transition_state(current: State, event: &str) -> ControlFlow<StateError, State> {
    match (current.clone(), event) {
        (State::Idle, "start") => {
            ControlFlow::Continue(State::Processing(0))
        }
        (State::Processing(retries), "complete") => {
            ControlFlow::Continue(State::Completed("Done".to_string()))
        }
        (State::Processing(retries), "retry") if retries < 3 => {
            ControlFlow::Continue(State::Processing(retries + 1))
        }
        (State::Processing(_), "retry") => {
            ControlFlow::Break(StateError::MaxRetriesExceeded)
        }
        (State::Processing(_), "fail") => {
            ControlFlow::Continue(State::Failed("Error".to_string()))
        }
        _ => {
            ControlFlow::Break(StateError::InvalidTransition(
                format!("{:?}", current),
                event.to_string()
            ))
        }
    }
}

// =============================================================================
// 实际应用场景
// =============================================================================

/// 配置解析器
#[derive(Debug)]
struct Config {
    host: String,
    port: u16,
    max_connections: u32,
}

#[derive(Debug)]
enum ConfigError {
    MissingField(&'static str),
    InvalidValue(&'static str, String),
    PortOutOfRange(u16),
}

fn parse_config(env_vars: &[(String, String)]) -> ControlFlow<ConfigError, Config> {
    let mut host = None;
    let mut port = None;
    let mut max_connections = None;
    
    for (key, value) in env_vars {
        match key.as_str() {
            "HOST" => host = Some(value.clone()),
            "PORT" => {
                match value.parse::<u16>() {
                    Ok(p) if p >= 1024 && p <= 65535 => port = Some(p),
                    Ok(p) => return ControlFlow::Break(ConfigError::PortOutOfRange(p)),
                    Err(_) => return ControlFlow::Break(ConfigError::InvalidValue(
                        "PORT", value.clone()
                    )),
                }
            }
            "MAX_CONNECTIONS" => {
                match value.parse::<u32>() {
                    Ok(c) => max_connections = Some(c),
                    Err(_) => return ControlFlow::Break(ConfigError::InvalidValue(
                        "MAX_CONNECTIONS", value.clone()
                    )),
                }
            }
            _ => {}
        }
    }
    
    let config = Config {
        host: match host {
            Some(h) => h,
            None => return ControlFlow::Break(ConfigError::MissingField("HOST")),
        },
        port: match port {
            Some(p) => p,
            None => return ControlFlow::Break(ConfigError::MissingField("PORT")),
        },
        max_connections: max_connections.unwrap_or(100),
    };
    
    ControlFlow::Continue(config)
}

/// 批量操作
fn batch_operation<T>(
    items: Vec<T>,
    operation: impl Fn(T) -> Result<(), String>
) -> ControlFlow<(usize, String), ()> {
    for (idx, item) in items.into_iter().enumerate() {
        if let Err(e) = operation(item) {
            return ControlFlow::Break((idx, e));
        }
    }
    ControlFlow::Continue(())
}

// =============================================================================
// 主函数
// =============================================================================

fn main() {
    println!("=== Rust 1.94 ControlFlow 演示 ===\n");
    
    // 1. 基础查找
    println!("1. 基础查找示例");
    let numbers = vec![1, 5, 3, 8, 2, 9];
    if let Some(&found) = find_first(&numbers, |&x| x > 5) {
        println!("找到第一个 > 5 的数: {}", found);
    }
    
    // 2. 验证管道
    println!("\n2. 用户注册验证");
    let valid_user = UserRegistration {
        username: "john_doe".to_string(),
        email: "john@example.com".to_string(),
        password: "Pass1234".to_string(),
        age: 25,
    };
    
    let invalid_user = UserRegistration {
        username: "ab".to_string(),
        email: "invalid-email".to_string(),
        password: "weak".to_string(),
        age: 16,
    };
    
    println!("验证有效用户:");
    let _ = register_user(valid_user);
    
    println!("\n验证无效用户:");
    let _ = register_user(invalid_user);
    
    // 3. 数据处理
    println!("\n3. 数据处理管道");
    let data = vec![
        DataItem { id: 1, value: 10.0, category: "A".to_string() },
        DataItem { id: 2, value: 20.0, category: "B".to_string() },
        DataItem { id: 3, value: 15.0, category: "C".to_string() },
    ];
    
    match process_data_pipeline(&data, 100.0) {
        ControlFlow::Continue(results) => {
            println!("处理成功，结果: {:?}", results);
        }
        ControlFlow::Break(err) => {
            println!("处理失败: {:?}", err);
        }
    }
    
    // 4. 迭代器短路
    println!("\n4. 迭代器短路");
    let nums = vec![10, 20, 30, 40, 50];
    match sum_until_limit(&nums, 80) {
        ControlFlow::Continue(sum) => println!("总和: {}", sum),
        ControlFlow::Break(exceeded) => println!("超过限制时的值: {}", exceeded),
    }
    
    // 5. 状态机
    println!("\n5. 状态机转换");
    let mut state = State::Idle;
    println!("初始状态: {:?}", state);
    
    state = match transition_state(state, "start") {
        ControlFlow::Continue(s) => s,
        ControlFlow::Break(e) => {
            println!("转换失败: {:?}", e);
            return;
        }
    };
    println!("开始后: {:?}", state);
    
    state = match transition_state(state, "complete") {
        ControlFlow::Continue(s) => s,
        ControlFlow::Break(e) => {
            println!("转换失败: {:?}", e);
            return;
        }
    };
    println!("完成后: {:?}", state);
    
    // 6. 配置解析
    println!("\n6. 配置解析");
    let env_vars = vec![
        ("HOST".to_string(), "localhost".to_string()),
        ("PORT".to_string(), "8080".to_string()),
        ("MAX_CONNECTIONS".to_string(), "1000".to_string()),
    ];
    
    match parse_config(&env_vars) {
        ControlFlow::Continue(config) => {
            println!("配置解析成功: {:?}", config);
        }
        ControlFlow::Break(err) => {
            println!("配置解析失败: {:?}", err);
        }
    }
    
    // 7. 批量操作
    println!("\n7. 批量操作");
    let items = vec![1, 2, 3, 4, 5];
    match batch_operation(items, |x| {
        if x == 3 {
            Err("不能处理3".to_string())
        } else {
            println!("处理: {}", x);
            Ok(())
        }
    }) {
        ControlFlow::Continue(_) => println!("批量操作成功"),
        ControlFlow::Break((idx, err)) => {
            println!("批量操作失败，索引 {}: {}", idx, err);
        }
    }
    
    println!("\n=== 演示完成 ===");
}
