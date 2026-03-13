//! 实际应用场景示例集合
//!
//! 本文件包含各种实际应用场景的示例，展示Rust在实际项目中的使用
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

/// Web服务器示例
pub fn web_server_example() {
    println!("🌐 Web服务器示例");

    // 模拟HTTP请求处理
    struct HttpRequest {
        method: String,
        path: String,
    }

    struct HttpResponse {
        status: u16,
        body: String,
    }

    fn handle_request(req: HttpRequest) -> HttpResponse {
        HttpResponse {
            status: 200,
            body: format!("处理请求: {} {}", req.method, req.path),
        }
    }

    let request = HttpRequest {
        method: "GET".to_string(),
        path: "/api/users".to_string(),
    };

    let response = handle_request(request);
    println!("  - 响应状态: {}", response.status);
    println!("  - 响应体: {}", response.body);
}

/// 数据处理管道示例
pub fn data_processing_pipeline_example() {
    println!("\n📊 数据处理管道示例");

    let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5];
    println!("  - 原始数据: {:?}", data);

    // 排序
    data.sort();
    println!("  - 排序后: {:?}", data);

    // 去重
    data.dedup();
    println!("  - 去重后: {:?}", data);

    // 过滤
    data.retain(|&x| x > 3);
    println!("  - 过滤后: {:?}", data);
}

/// 并发任务处理示例
pub fn concurrent_task_processing_example() {
    println!("\n⚡ 并发任务处理示例");

    use std::sync::{Arc, Mutex};

    let tasks = Arc::new(Mutex::new(vec![1, 2, 3, 4, 5]));
    let results = Arc::new(Mutex::new(Vec::new()));
    let mut handles = vec![];

    for i in 0..5 {
        let tasks = Arc::clone(&tasks);
        let results = Arc::clone(&results);
        let handle = thread::spawn(move || {
            let task = {
                let mut tasks = tasks.lock().unwrap();
                tasks.pop()
            };
            if let Some(task) = task {
                let result = task * 2;
                let mut results = results.lock().unwrap();
                results.push(result);
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    let final_results = results.lock().unwrap();
    println!("  - 处理结果: {:?}", *final_results);
}

/// 配置管理示例
pub fn configuration_management_example() {
    println!("\n⚙️ 配置管理示例");

    use std::collections::HashMap;

    struct Config {
        settings: HashMap<String, String>,
    }

    impl Config {
        fn new() -> Self {
            Config {
                settings: HashMap::new(),
            }
        }

        fn set(&mut self, key: String, value: String) {
            self.settings.insert(key, value);
        }

        fn get(&self, key: &str) -> Option<&String> {
            self.settings.get(key)
        }
    }

    let mut config = Config::new();
    config.set("host".to_string(), "localhost".to_string());
    config.set("port".to_string(), "8080".to_string());

    println!("  - 主机: {:?}", config.get("host"));
    println!("  - 端口: {:?}", config.get("port"));
}

/// 错误处理示例
pub fn error_handling_example() {
    println!("\n🛡️ 错误处理示例");

    fn process_data(data: &str) -> Result<i32, String> {
        data.parse::<i32>()
            .map_err(|e| format!("解析错误: {}", e))
    }

    match process_data("42") {
        Ok(value) => println!("  - 成功: {}", value),
        Err(e) => println!("  - 错误: {}", e),
    }

    match process_data("invalid") {
        Ok(value) => println!("  - 成功: {}", value),
        Err(e) => println!("  - 错误: {}", e),
    }
}

/// 主函数
fn main() {
    println!("🚀 Rust 实际应用场景示例集合");
    println!("============================\n");

    web_server_example();
    data_processing_pipeline_example();
    concurrent_task_processing_example();
    configuration_management_example();
    error_handling_example();

    println!("\n✅ 所有实际应用场景示例完成！");
}
