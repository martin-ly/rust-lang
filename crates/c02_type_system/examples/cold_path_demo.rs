//! Rust 1.95.0 `core::hint::cold_path` 专题示例
//!
//! `core::hint::cold_path()` 是 Rust 1.95.0 稳定化的分支预测提示，
//! 告诉编译器"当前代码路径很少执行"，辅助优化指令布局和分支预测。
//!
//! 权威来源: https://releases.rs/docs/1.95.0/
//!
//! 运行方式:
//! ```bash
//! cargo run --example cold_path_demo -p c02_type_system
//! ```

use std::collections::HashMap;
use std::hint::cold_path;

// ==================== 示例 1: 基础用法 — 错误处理冷路径 ====================

/// 使用 `cold_path()` 标注错误处理分支
fn parse_number(input: &str) -> Result<i32, &'static str> {
    match input.parse::<i32>() {
        Ok(n) => Ok(n),
        Err(_) => {
            cold_path(); // 解析失败是异常情况
            Err("invalid number")
        }
    }
}

fn demo_basic_cold_path() {
    println!("--- cold_path 基础: 错误处理分支 ---");

    // 热路径: 正常输入
    let result = parse_number("42");
    println!("  parse '42': {:?}", result);
    assert_eq!(result, Ok(42));

    // 冷路径: 错误输入
    let result = parse_number("not_a_number");
    println!("  parse 'not_a_number': {:?}", result);
    assert!(result.is_err());

    println!("  ✅ cold_path() 提示编译器: Err 分支很少执行");
}

// ==================== 示例 2: 缓存查找 — 命中 vs 未命中 ====================

/// 使用 `cold_path()` 优化缓存查找的冷路径
struct Cache {
    data: HashMap<u64, String>,
}

impl Cache {
    fn get_or_compute<F>(&mut self, key: u64, compute: F) -> String
    where
        F: FnOnce() -> String,
    {
        if let Some(value) = self.data.get(&key) {
            // 热路径: 缓存命中
            value.clone()
        } else {
            cold_path(); // 冷路径: 缓存未命中
            let new_value = compute();
            self.data.insert(key, new_value.clone());
            new_value
        }
    }
}

fn demo_cache_lookup() {
    println!("\n--- cold_path: 缓存查找优化 ---");

    let mut cache = Cache {
        data: HashMap::new(),
    };

    // 预热缓存
    cache.data.insert(1, "preloaded".to_string());

    // 热路径: 缓存命中
    let v1 = cache.get_or_compute(1, || unreachable!());
    println!("  缓存命中 key=1: {}", v1);

    // 冷路径: 缓存未命中
    let v2 = cache.get_or_compute(2, || "computed".to_string());
    println!("  缓存未命中 key=2: {}", v2);

    // 再次命中
    let v3 = cache.get_or_compute(2, || unreachable!());
    println!("  再次命中 key=2: {}", v3);

    assert_eq!(v1, "preloaded");
    assert_eq!(v2, "computed");
    assert_eq!(v3, "computed");
}

// ==================== 示例 3: 限流/熔断器的冷路径 ====================

/// 限流器: 正常请求为热路径，限流触发为冷路径
struct RateLimiter {
    requests: u32,
    max_requests: u32,
}

impl RateLimiter {
    fn allow(&mut self) -> bool {
        if self.requests < self.max_requests {
            // 热路径: 允许通过
            self.requests += 1;
            true
        } else {
            cold_path(); // 冷路径: 触发限流
            false
        }
    }

    #[allow(dead_code)]
    fn reset(&mut self) {
        self.requests = 0;
    }
}

fn demo_rate_limiter() {
    println!("\n--- cold_path: 限流器 ---");

    let mut limiter = RateLimiter {
        requests: 0,
        max_requests: 3,
    };

    for i in 1..=5 {
        let allowed = limiter.allow();
        println!(
            "  请求 {}: {}",
            i,
            if allowed {
                "ALLOWED ✅"
            } else {
                "BLOCKED ❌"
            }
        );
    }

    assert!(!limiter.allow());
}

// ==================== 示例 4: 与 #[cold] 函数的对比 ====================

/// `#[cold]` 属性标记整个函数为冷路径
#[cold]
fn handle_critical_error() {
    eprintln!("[CRITICAL] 系统级错误发生，启动恢复流程...");
    // 复杂的错误恢复逻辑...
}

/// `cold_path()` 在分支内部标注
fn process_request(req: Option<&str>) -> &str {
    if let Some(r) = req {
        // 热路径
        r
    } else {
        cold_path(); // 标注此分支为冷路径
        handle_critical_error();
        "default"
    }
}

fn demo_cold_attribute_vs_hint() {
    println!("\n--- cold_path() vs #[cold] 对比 ---");

    let result = process_request(Some("valid"));
    println!("  正常请求: {}", result);

    let result = process_request(None);
    println!("  无效请求: {}", result);

    println!("  对比:");
    println!("    - #[cold]: 标记整个函数，编译器将其放在代码段末尾");
    println!("    - cold_path(): 标记分支，告诉 CPU 分支预测器此路径不太可能");
    println!("    - 两者互补: #[cold] 优化代码布局，cold_path() 优化运行时预测");
}

// ==================== 示例 5: 循环中的罕见条件 ====================

/// 在循环中标注罕见条件分支
fn demo_loop_rare_condition() {
    println!("\n--- cold_path: 循环中的罕见条件 ---");

    let values: Vec<i32> = (1..=20).collect();
    let mut special_count = 0;

    for v in &values {
        if v % 17 == 0 {
            cold_path(); // 17 的倍数很少出现
            special_count += 1;
            println!("  发现特殊值: {} (17 的倍数)", v);
        }
        // 热路径: 普通处理（无输出，避免刷屏）
    }

    println!("  总特殊值数量: {}", special_count);
    assert_eq!(special_count, 1); // 只有 17
}

// ==================== 示例 6: 配置解析 — 默认值 vs 自定义值 ====================

/// 配置查找: 使用默认值是热路径，自定义值是冷路径
fn demo_config_lookup() {
    println!("\n--- cold_path: 配置解析优化 ---");

    let mut config: HashMap<&str, &str> = HashMap::new();
    // 大部分用户使用默认配置，少数自定义
    config.insert("timeout", "30s"); // 自定义（冷路径）

    fn get_config<'a>(cfg: &HashMap<&str, &'a str>, key: &str, default: &'a str) -> &'a str {
        match cfg.get(key) {
            Some(v) => {
                cold_path(); // 自定义配置是少数
                v
            }
            None => default, // 热路径: 使用默认值
        }
    }

    let timeout = get_config(&config, "timeout", "10s");
    println!("  timeout: {} (自定义)", timeout);

    let retries = get_config(&config, "retries", "3");
    println!("  retries: {} (默认)", retries);

    assert_eq!(timeout, "30s");
    assert_eq!(retries, "3");
}

// ==================== 主演示函数 ====================

fn main() {
    println!("🦀 Rust 1.95.0 `core::hint::cold_path` 专题演示\n");
    println!("说明: cold_path() 告诉编译器'此分支很少执行'\n");

    demo_basic_cold_path();
    demo_cache_lookup();
    demo_rate_limiter();
    demo_cold_attribute_vs_hint();
    demo_loop_rare_condition();
    demo_config_lookup();

    println!("\n✅ `cold_path` 演示完成！");
    println!("   关键要点:");
    println!("   - cold_path() 是编译器提示，不影响程序语义");
    println!("   - 影响代码布局: 冷路径代码被移到函数末尾");
    println!("   - 影响分支预测: CPU 更倾向预测热路径");
    println!("   - 适用场景: 错误处理、缓存未命中、限流触发、罕见条件");
    println!("   - 与 #[cold] 互补: #[cold] 标记函数，cold_path() 标记分支");
    println!("   - ⚠️ 不要滥用: 错误标注会恶化分支预测，降低性能");
}
