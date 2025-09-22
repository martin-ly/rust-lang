//! 性能基准测试套件
//! 
//! 提供全面的性能测试，包括推理性能、缓存性能、存储性能等

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use c19_ai::*;
use std::sync::Arc;
use tokio::runtime::Runtime;
use std::time::Duration;

/// 推理性能基准测试
fn benchmark_inference_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("inference_performance");
    group.measurement_time(Duration::from_secs(10));
    
    // 测试不同批次大小的推理性能
    for batch_size in [1, 10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("batch_inference", batch_size),
            batch_size,
            |b, &batch_size| {
                b.to_async(&rt).iter(|| async {
                    // 模拟推理请求
                    let requests = (0..batch_size)
                        .map(|i| InferenceRequest {
                            model_id: "test_model".to_string(),
                            input: serde_json::json!({
                                "data": format!("input_data_{}", i),
                                "batch_id": i
                            }),
                        })
                        .collect::<Vec<_>>();
                    
                    // 执行推理
                    for request in requests {
                        black_box(process_inference_request(request).await);
                    }
                })
            },
        );
    }
    
    group.finish();
}

/// 缓存性能基准测试
fn benchmark_cache_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("cache_performance");
    group.measurement_time(Duration::from_secs(10));
    
    // 测试缓存命中性能
    group.bench_function("cache_hit", |b| {
        b.to_async(&rt).iter(|| async {
            let cache = create_test_cache().await;
            let key = "test_key";
            let value = "test_value";
            
            // 先设置缓存
            cache.set(key, value, Duration::from_secs(60)).await.unwrap();
            
            // 测试缓存命中
            let result = cache.get(key).await.unwrap();
            black_box(result);
        })
    });
    
    // 测试缓存未命中性能
    group.bench_function("cache_miss", |b| {
        b.to_async(&rt).iter(|| async {
            let cache = create_test_cache().await;
            let key = "non_existent_key";
            
            let result = cache.get(key).await;
            black_box(result);
        })
    });
    
    // 测试缓存写入性能
    group.bench_function("cache_set", |b| {
        b.to_async(&rt).iter(|| async {
            let cache = create_test_cache().await;
            let key = format!("key_{}", rand::random::<u32>());
            let value = "test_value";
            
            cache.set(&key, value, Duration::from_secs(60)).await.unwrap();
        })
    });
    
    group.finish();
}

/// 存储性能基准测试
fn benchmark_storage_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("storage_performance");
    group.measurement_time(Duration::from_secs(10));
    
    // 测试文件上传性能
    for file_size in [1024, 10240, 102400, 1048576].iter() {
        group.bench_with_input(
            BenchmarkId::new("file_upload", file_size),
            file_size,
            |b, &file_size| {
                b.to_async(&rt).iter(|| async {
                    let storage = create_test_storage().await;
                    let key = format!("test_file_{}.bin", rand::random::<u32>());
                    let data = vec![0u8; file_size];
                    
                    storage.put(&key, data).await.unwrap();
                })
            },
        );
    }
    
    // 测试文件下载性能
    group.bench_function("file_download", |b| {
        b.to_async(&rt).iter(|| async {
            let storage = create_test_storage().await;
            let key = "test_download_file";
            
            // 先上传文件
            let data = vec![0u8; 1024];
            storage.put(key, data).await.unwrap();
            
            // 测试下载
            let result = storage.get(key).await.unwrap();
            black_box(result);
        })
    });
    
    group.finish();
}

/// 数据库性能基准测试
fn benchmark_database_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("database_performance");
    group.measurement_time(Duration::from_secs(10));
    
    // 测试批量插入性能
    for batch_size in [10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("batch_insert", batch_size),
            batch_size,
            |b, &batch_size| {
                b.to_async(&rt).iter(|| async {
                    let db = create_test_database().await;
                    
                    for i in 0..batch_size {
                        let user = create_test_user(i);
                        db.insert_user(&user).await.unwrap();
                    }
                })
            },
        );
    }
    
    // 测试查询性能
    group.bench_function("query_performance", |b| {
        b.to_async(&rt).iter(|| async {
            let db = create_test_database().await;
            
            // 先插入测试数据
            for i in 0..1000 {
                let user = create_test_user(i);
                db.insert_user(&user).await.unwrap();
            }
            
            // 测试查询
            let users = db.get_users_by_role("user").await.unwrap();
            black_box(users);
        })
    });
    
    group.finish();
}

/// 并发性能基准测试
fn benchmark_concurrent_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("concurrent_performance");
    group.measurement_time(Duration::from_secs(10));
    
    // 测试并发推理性能
    for concurrency in [10, 50, 100, 500].iter() {
        group.bench_with_input(
            BenchmarkId::new("concurrent_inference", concurrency),
            concurrency,
            |b, &concurrency| {
                b.to_async(&rt).iter(|| async {
                    let handles = (0..concurrency)
                        .map(|i| {
                            tokio::spawn(async move {
                                let request = InferenceRequest {
                                    model_id: "test_model".to_string(),
                                    input: serde_json::json!({
                                        "data": format!("concurrent_input_{}", i)
                                    }),
                                };
                                process_inference_request(request).await
                            })
                        })
                        .collect::<Vec<_>>();
                    
                    for handle in handles {
                        let result = handle.await.unwrap();
                        black_box(result);
                    }
                })
            },
        );
    }
    
    group.finish();
}

/// 内存使用性能基准测试
fn benchmark_memory_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("memory_performance");
    group.measurement_time(Duration::from_secs(10));
    
    // 测试大模型加载性能
    group.bench_function("large_model_loading", |b| {
        b.to_async(&rt).iter(|| async {
            let model_registry = create_test_model_registry().await;
            let model_data = vec![0u8; 100 * 1024 * 1024]; // 100MB
            
            let model = ModelEntry {
                id: "large_model".to_string(),
                name: "Large Test Model".to_string(),
                version: "1.0.0".to_string(),
                model_type: ModelType::MachineLearning,
                framework: Some("pytorch".to_string()),
                path: Some("large_model.bin".to_string()),
                device: Some("cpu".to_string()),
                precision: Some("fp32".to_string()),
                metadata: serde_json::json!({
                    "size": model_data.len(),
                    "parameters": 1000000
                }),
                created_at: chrono::Utc::now(),
                updated_at: chrono::Utc::now(),
            };
            
            model_registry.register_model(model).await.unwrap();
        })
    });
    
    // 测试内存清理性能
    group.bench_function("memory_cleanup", |b| {
        b.to_async(&rt).iter(|| async {
            let cache = create_test_cache().await;
            
            // 填充缓存
            for i in 0..10000 {
                let key = format!("memory_test_key_{}", i);
                let value = format!("memory_test_value_{}", i);
                cache.set(&key, &value, Duration::from_secs(60)).await.unwrap();
            }
            
            // 清理缓存
            cache.clear().await.unwrap();
        })
    });
    
    group.finish();
}

/// 网络性能基准测试
fn benchmark_network_performance(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    let mut group = c.benchmark_group("network_performance");
    group.measurement_time(Duration::from_secs(10));
    
    // 测试API响应性能
    group.bench_function("api_response", |b| {
        b.to_async(&rt).iter(|| async {
            let app = create_test_api_app().await;
            
            // 模拟API请求
            let request = create_test_api_request();
            let response = app.handle_request(request).await.unwrap();
            black_box(response);
        })
    });
    
    // 测试WebSocket性能
    group.bench_function("websocket_performance", |b| {
        b.to_async(&rt).iter(|| async {
            let ws_manager = create_test_websocket_manager().await;
            
            // 模拟WebSocket消息
            let message = WebSocketMessage {
                id: "test_message".to_string(),
                message_type: WebSocketMessageType::Text,
                content: "test_content".to_string(),
                timestamp: chrono::Utc::now(),
                sender_id: "test_sender".to_string(),
                room_id: Some("test_room".to_string()),
            };
            
            ws_manager.broadcast_message("test_room", message).await.unwrap();
        })
    });
    
    group.finish();
}

// 辅助函数

async fn process_inference_request(request: InferenceRequest) -> InferenceResponse {
    // 模拟推理处理
    tokio::time::sleep(Duration::from_millis(1)).await;
    
    InferenceResponse {
        id: format!("response_{}", rand::random::<u32>()),
        model_id: request.model_id,
        result: serde_json::json!({
            "prediction": "test_result",
            "confidence": 0.95
        }),
        confidence: 0.95,
        processing_time: 1,
        created_at: chrono::Utc::now().to_rfc3339(),
    }
}

async fn create_test_cache() -> Arc<MemoryCache> {
    Arc::new(MemoryCache::new(1000, Duration::from_secs(60)))
}

async fn create_test_storage() -> Arc<LocalStorage> {
    Arc::new(LocalStorage::new("/tmp/benchmark_storage").await.unwrap())
}

async fn create_test_database() -> Arc<DatabaseManager> {
    Arc::new(DatabaseManager::new("sqlite::memory:").await.unwrap())
}

fn create_test_user(id: u32) -> User {
    User {
        id: format!("user_{}", id),
        username: format!("user_{}", id),
        email: format!("user{}@example.com", id),
        password_hash: "hashed_password".to_string(),
        roles: vec!["user".to_string()],
        is_active: true,
        is_verified: true,
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
        last_login: None,
        failed_login_attempts: 0,
        locked_until: None,
        two_factor_enabled: false,
        two_factor_secret: None,
    }
}

async fn create_test_model_registry() -> Arc<ModelRegistry> {
    Arc::new(ModelRegistry::new())
}

async fn create_test_api_app() -> Arc<ApiApp> {
    Arc::new(ApiApp::new().await.unwrap())
}

fn create_test_api_request() -> ApiRequest {
    ApiRequest {
        method: "GET".to_string(),
        path: "/api/v1/health".to_string(),
        headers: std::collections::HashMap::new(),
        body: None,
    }
}

async fn create_test_websocket_manager() -> Arc<WebSocketManager> {
    Arc::new(WebSocketManager::new())
}

// 基准测试组配置
criterion_group!(
    benches,
    benchmark_inference_performance,
    benchmark_cache_performance,
    benchmark_storage_performance,
    benchmark_database_performance,
    benchmark_concurrent_performance,
    benchmark_memory_performance,
    benchmark_network_performance
);

criterion_main!(benches);
