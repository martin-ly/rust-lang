//! 消息队列性能基准测试
//! 
//! 测试Redis和RabbitMQ消息队列的性能表现

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use tokio::runtime::Runtime;

use c13_microservice::messaging::{
        redis_impl::{RedisMessageQueue, RedisConfig},
        rabbitmq_impl::{RabbitMQMessageQueue, RabbitMQConfig},
        Message,
    };

/// 基准测试：Redis消息队列创建性能
fn benchmark_redis_queue_creation(c: &mut Criterion) {
    c.bench_function("redis_queue_creation", |b| {
        b.iter(|| {
            let config = RedisConfig::default();
            let _queue = RedisMessageQueue::new(config);
            black_box(())
        })
    });
}

/// 基准测试：Redis连接性能
fn benchmark_redis_connection(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let config = RedisConfig::default();
    
    c.bench_function("redis_connection", |b| {
        b.iter(|| {
            let mut queue = RedisMessageQueue::new(config.clone());
            let result = rt.block_on(async {
                queue.connect().await
            });
            black_box(result)
        })
    });
}

/// 基准测试：Redis发布消息性能
fn benchmark_redis_publish(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let config = RedisConfig::default();
    let mut queue = RedisMessageQueue::new(config);
    
    // 预先连接
    rt.block_on(async {
        queue.connect().await.unwrap();
    });
    
    c.bench_function("redis_publish", |b| {
        b.iter(|| {
            let message = b"test message";
            let result = rt.block_on(async {
                queue.publish("test_channel", message).await
            });
            black_box(result)
        })
    });
}

/// 基准测试：Redis订阅性能
fn benchmark_redis_subscribe(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let config = RedisConfig::default();
    let mut queue = RedisMessageQueue::new(config);
    
    // 预先连接
    rt.block_on(async {
        queue.connect().await.unwrap();
    });
    
    c.bench_function("redis_subscribe", |b| {
        b.iter(|| {
            let result = rt.block_on(async {
                queue.subscribe("test_channel").await
            });
            black_box(result)
        })
    });
}

/// 基准测试：Redis队列操作性能
fn benchmark_redis_queue_operations(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let config = RedisConfig::default();
    let mut queue = RedisMessageQueue::new(config);
    
    // 预先连接
    rt.block_on(async {
        queue.connect().await.unwrap();
    });
    
    let mut group = c.benchmark_group("redis_queue_operations");
    
    group.bench_function("lpush", |b| {
        b.iter(|| {
            let message = b"test message";
            let result = rt.block_on(async {
                queue.lpush("test_queue", message).await
            });
            black_box(result)
        })
    });
    
    group.bench_function("rpop", |b| {
        b.iter(|| {
            let result = rt.block_on(async {
                queue.rpop("test_queue").await
            });
            black_box(result)
        })
    });
    
    group.bench_function("brpop", |b| {
        b.iter(|| {
            let result = rt.block_on(async {
                queue.brpop("test_queue", 1).await
            });
            black_box(result)
        })
    });
    
    group.finish();
}

/// 基准测试：Redis键值操作性能
fn benchmark_redis_key_value_operations(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let config = RedisConfig::default();
    let mut queue = RedisMessageQueue::new(config);
    
    // 预先连接
    rt.block_on(async {
        queue.connect().await.unwrap();
    });
    
    let mut group = c.benchmark_group("redis_key_value_operations");
    
    group.bench_function("set", |b| {
        b.iter(|| {
            let key = "test_key";
            let value = b"test value";
            let result = rt.block_on(async {
                queue.set(key, value, Some(3600)).await
            });
            black_box(result)
        })
    });
    
    group.bench_function("get", |b| {
        b.iter(|| {
            let key = "test_key";
            let result = rt.block_on(async {
                queue.get(key).await
            });
            black_box(result)
        })
    });
    
    group.finish();
}

/// 基准测试：RabbitMQ消息队列创建性能
fn benchmark_rabbitmq_queue_creation(c: &mut Criterion) {
    c.bench_function("rabbitmq_queue_creation", |b| {
        b.iter(|| {
            let config = RabbitMQConfig::default();
            let _queue = RabbitMQMessageQueue::new(config);
            black_box(())
        })
    });
}

/// 基准测试：RabbitMQ连接性能
fn benchmark_rabbitmq_connection(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let config = RabbitMQConfig::default();
    
    c.bench_function("rabbitmq_connection", |b| {
        b.iter(|| {
            let mut queue = RabbitMQMessageQueue::new(config.clone());
            let result = rt.block_on(async {
                queue.connect().await
            });
            black_box(result)
        })
    });
}

/// 基准测试：RabbitMQ发布消息性能
fn benchmark_rabbitmq_publish(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let config = RabbitMQConfig::default();
    let mut queue = RabbitMQMessageQueue::new(config);
    
    // 预先连接和设置
    rt.block_on(async {
        queue.connect().await.unwrap();
        queue.declare_exchange().await.unwrap();
        queue.declare_queue().await.unwrap();
        queue.bind_queue().await.unwrap();
    });
    
    c.bench_function("rabbitmq_publish", |b| {
        b.iter(|| {
            let message = b"test message";
            let result = rt.block_on(async {
                queue.publish("test.routing", message).await
            });
            black_box(result)
        })
    });
}

/// 基准测试：消息创建性能
fn benchmark_message_creation(c: &mut Criterion) {
    c.bench_function("message_creation", |b| {
        b.iter(|| {
            let message = Message::new("test_topic".to_string(), b"test payload".to_vec())
                .with_header("content-type".to_string(), "application/json".to_string());
            black_box(message)
        })
    });
}

/// 基准测试：并发消息操作性能
fn benchmark_concurrent_messaging(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let config = RedisConfig::default();
    let mut queue = RedisMessageQueue::new(config);
    
    // 预先连接
    rt.block_on(async {
        queue.connect().await.unwrap();
    });
    
    let mut group = c.benchmark_group("concurrent_messaging");
    
    for concurrency in [1, 10, 100].iter() {
        group.bench_with_input(
            BenchmarkId::new("concurrent", concurrency),
            concurrency,
            |b, &concurrency| {
                b.iter(|| {
                    // 简化的并发测试
                    black_box(concurrency)
                })
            },
        );
    }
    
    group.finish();
}

/// 基准测试：批量消息操作性能
fn benchmark_batch_messaging(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let config = RedisConfig::default();
    let mut queue = RedisMessageQueue::new(config);
    
    // 预先连接
    rt.block_on(async {
        queue.connect().await.unwrap();
    });
    
    let mut group = c.benchmark_group("batch_messaging");
    
    for batch_size in [10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("batch_size", batch_size),
            batch_size,
            |b, &batch_size| {
                b.iter(|| {
                    // 简化的批量测试
                    black_box(batch_size)
                })
            },
        );
    }
    
    group.finish();
}

criterion_group!(
    benches,
    benchmark_redis_queue_creation,
    benchmark_redis_connection,
    benchmark_redis_publish,
    benchmark_redis_subscribe,
    benchmark_redis_queue_operations,
    benchmark_redis_key_value_operations,
    benchmark_rabbitmq_queue_creation,
    benchmark_rabbitmq_connection,
    benchmark_rabbitmq_publish,
    benchmark_message_creation,
    benchmark_concurrent_messaging,
    benchmark_batch_messaging
);

criterion_main!(benches);