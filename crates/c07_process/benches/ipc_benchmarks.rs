//! C07 进程间通信（IPC）性能基准测试
//!
//! 测试消息传递、进程配置创建和同步原语的性能。

use c07_process::{
    IpcConfig, IpcManager, IpcProtocol, Message, ProcessConfig, ProcessManager, ResourceLimits,
};
use criterion::{Criterion, criterion_group, criterion_main};
use std::collections::HashMap;
use std::time::Duration;

/// 基准测试：IPC 消息创建与序列化
fn bench_ipc_message_creation(c: &mut Criterion) {
    c.bench_function("ipc_message_creation", |b| {
        b.iter(|| {
            let msg = Message::new(
                1u64,
                "benchmark_channel",
                b"Hello, IPC Benchmark!".to_vec(),
                42u32,
            );
            std::hint::black_box(msg);
        });
    });
}

/// 基准测试：进程配置创建
fn bench_process_config_creation(c: &mut Criterion) {
    c.bench_function("process_config_creation", |b| {
        let mut env = HashMap::new();
        env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
        env.insert("HOME".to_string(), "/tmp".to_string());

        b.iter(|| {
            let config = ProcessConfig {
                program: "echo".to_string(),
                args: vec!["benchmark".to_string()],
                env: env.clone(),
                working_dir: Some("/tmp".to_string()),
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            };
            std::hint::black_box(config);
        });
    });
}

/// 基准测试：IPC 管理器初始化
fn bench_ipc_manager_init(c: &mut Criterion) {
    c.bench_function("ipc_manager_init", |b| {
        b.iter(|| {
            let config = IpcConfig {
                protocol: IpcProtocol::MessageQueue,
                timeout: Duration::from_millis(1000),
                retry_count: 3,
                buffer_size: 4096,
                encrypted: false,
            };
            let manager = IpcManager::new(config);
            std::hint::black_box(manager);
        });
    });
}

/// 基准测试：进程管理器创建
fn bench_process_manager_creation(c: &mut Criterion) {
    c.bench_function("process_manager_creation", |b| {
        b.iter(|| {
            let manager = ProcessManager::new();
            std::hint::black_box(manager);
        });
    });
}

/// 基准测试：ResourceLimits 默认创建
fn bench_resource_limits_default(c: &mut Criterion) {
    c.bench_function("resource_limits_default", |b| {
        b.iter(|| {
            let limits = ResourceLimits::default();
            std::hint::black_box(limits);
        });
    });
}

/// 基准测试：HashMap 环境变量克隆（进程创建常见开销）
fn bench_env_hashmap_clone(c: &mut Criterion) {
    let mut env = HashMap::new();
    for i in 0..50 {
        env.insert(format!("KEY_{}", i), format!("VALUE_{}", i));
    }

    c.bench_function("env_hashmap_clone", |b| {
        b.iter(|| {
            let cloned = env.clone();
            std::hint::black_box(cloned);
        });
    });
}

criterion_group!(
    benches,
    bench_ipc_message_creation,
    bench_process_config_creation,
    bench_ipc_manager_init,
    bench_process_manager_creation,
    bench_resource_limits_default,
    bench_env_hashmap_clone,
);
criterion_main!(benches);
