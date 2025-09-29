//! AI集成异步演示
//! 
//! 本示例展示了异步编程在AI应用中的使用：
//! - 异步AI模型推理
//! - 批量处理
//! - 流式处理
//! - 模型管理
//! - 推理缓存
//! - 异步训练
//! - 模型版本管理
//! - AI服务编排
//! 
//! 运行方式：
//! ```bash
//! cargo run --example ai_integration_demo
//! ```

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock, mpsc, Semaphore};
use tokio::time::sleep;
use serde::{Serialize, Deserialize};
use anyhow::Result;
use uuid::Uuid;

/// AI模型信息
#[derive(Debug, Clone)]
pub struct ModelInfo {
    pub id: String,
    pub name: String,
    pub version: String,
    pub model_type: ModelType,
    pub input_shape: Vec<usize>,
    pub output_shape: Vec<usize>,
    pub parameters: HashMap<String, f32>,
    pub created_at: Instant,
    pub last_updated: Instant,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModelType {
    Classification,
    Regression,
    Generation,
    Embedding,
    Translation,
}

impl std::fmt::Display for ModelType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ModelType::Classification => write!(f, "Classification"),
            ModelType::Regression => write!(f, "Regression"),
            ModelType::Generation => write!(f, "Generation"),
            ModelType::Embedding => write!(f, "Embedding"),
            ModelType::Translation => write!(f, "Translation"),
        }
    }
}

/// 推理请求
#[derive(Debug, Clone)]
pub struct InferenceRequest {
    pub id: String,
    pub model_id: String,
    pub input_data: Vec<f32>,
    pub priority: InferencePriority,
    pub timeout: Duration,
    pub metadata: HashMap<String, String>,
    pub created_at: Instant,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum InferencePriority {
    Low = 1,
    Normal = 2,
    High = 3,
    Critical = 4,
}

/// 推理结果
#[derive(Debug, Clone)]
pub struct InferenceResult {
    pub request_id: String,
    pub model_id: String,
    pub output_data: Vec<f32>,
    pub confidence: f32,
    pub processing_time: Duration,
    pub metadata: HashMap<String, String>,
    pub completed_at: Instant,
}

/// 异步AI模型
pub struct AsyncAIModel {
    info: ModelInfo,
    inference_queue: Arc<Mutex<VecDeque<InferenceRequest>>>,
    result_cache: Arc<RwLock<HashMap<String, InferenceResult>>>,
    max_concurrent_inferences: usize,
    semaphore: Arc<Semaphore>,
}

impl AsyncAIModel {
    pub fn new(info: ModelInfo, max_concurrent_inferences: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent_inferences)),
            info,
            inference_queue: Arc::new(Mutex::new(VecDeque::new())),
            result_cache: Arc::new(RwLock::new(HashMap::new())),
            max_concurrent_inferences,
        }
    }

    pub async fn inference(&self, request: InferenceRequest) -> Result<InferenceResult> {
        // 检查缓存
        if let Some(cached_result) = self.get_cached_result(&request).await {
            return Ok(cached_result);
        }

        // 获取信号量许可
        let _permit = self.semaphore.acquire().await?;

        // 执行推理
        let start_time = Instant::now();
        let output_data = self.run_inference(&request.input_data).await?;
        let processing_time = start_time.elapsed();

        // 计算置信度（简化实现）
        let confidence = self.calculate_confidence(&output_data).await;

        let result = InferenceResult {
            request_id: request.id.clone(),
            model_id: request.model_id.clone(),
            output_data,
            confidence,
            processing_time,
            metadata: HashMap::new(),
            completed_at: Instant::now(),
        };

        // 缓存结果
        self.cache_result(&request, &result).await;

        Ok(result)
    }

    async fn get_cached_result(&self, request: &InferenceRequest) -> Option<InferenceResult> {
        let cache_key = self.generate_cache_key(request);
        let cache = self.result_cache.read().await;
        cache.get(&cache_key).cloned()
    }

    async fn cache_result(&self, request: &InferenceRequest, result: &InferenceResult) {
        let cache_key = self.generate_cache_key(request);
        let mut cache = self.result_cache.write().await;
        cache.insert(cache_key, result.clone());
    }

    fn generate_cache_key(&self, request: &InferenceRequest) -> String {
        // 简化的缓存键生成
        format!("{}:{:?}", request.model_id, request.input_data)
    }

    async fn run_inference(&self, _input_data: &[f32]) -> Result<Vec<f32>> {
        // 模拟AI模型推理
        let inference_time = Duration::from_millis(50 + rand::random::<u64>() % 200);
        sleep(inference_time).await;

        // 根据模型类型生成不同的输出
        let output_size = match self.info.model_type {
            ModelType::Classification => 10, // 10个类别
            ModelType::Regression => 1,      // 1个回归值
            ModelType::Generation => 512,    // 512个token
            ModelType::Embedding => 768,     // 768维嵌入
            ModelType::Translation => 256,   // 256个翻译token
        };

        let mut output = Vec::with_capacity(output_size);
        for _ in 0..output_size {
            output.push(rand::random::<f32>());
        }

        Ok(output)
    }

    async fn calculate_confidence(&self, output_data: &[f32]) -> f32 {
        // 简化的置信度计算
        let max_value = output_data.iter().fold(0.0f32, |acc, &x| acc.max(x.abs()));
        (max_value / (max_value + 1.0) * 100.0).min(100.0)
    }

    pub async fn batch_inference(&self, requests: Vec<InferenceRequest>) -> Result<Vec<InferenceResult>> {
        let mut results = Vec::with_capacity(requests.len());
        let mut handles = Vec::new();

        for request in requests {
            let model = self.clone();
            let handle = tokio::spawn(async move {
                model.inference(request).await
            });
            handles.push(handle);
        }

        for handle in handles {
            let result = handle.await??;
            results.push(result);
        }

        Ok(results)
    }

    pub async fn get_stats(&self) -> ModelStats {
        let queue_size = self.inference_queue.lock().await.len();
        let cache_size = self.result_cache.read().await.len();
        let available_permits = self.semaphore.available_permits();

        ModelStats {
            model_id: self.info.id.clone(),
            queue_size,
            cache_size,
            available_permits,
            total_permits: self.max_concurrent_inferences,
        }
    }
}

impl Clone for AsyncAIModel {
    fn clone(&self) -> Self {
        Self {
            info: self.info.clone(),
            inference_queue: Arc::clone(&self.inference_queue),
            result_cache: Arc::clone(&self.result_cache),
            max_concurrent_inferences: self.max_concurrent_inferences,
            semaphore: Arc::clone(&self.semaphore),
        }
    }
}

#[derive(Debug)]
pub struct ModelStats {
    pub model_id: String,
    pub queue_size: usize,
    pub cache_size: usize,
    pub available_permits: usize,
    pub total_permits: usize,
}

/// AI模型管理器
pub struct AIModelManager {
    models: Arc<RwLock<HashMap<String, AsyncAIModel>>>,
    model_versions: Arc<RwLock<HashMap<String, Vec<String>>>>,
}

impl AIModelManager {
    pub fn new() -> Self {
        Self {
            models: Arc::new(RwLock::new(HashMap::new())),
            model_versions: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub async fn register_model(&self, model: AsyncAIModel) -> Result<()> {
        let model_id = model.info.id.clone();
        let model_name = model.info.name.clone();
        let version = model.info.version.clone();

        // 注册模型
        {
            let mut models = self.models.write().await;
            models.insert(model_id.clone(), model);
        }

        // 更新版本信息
        {
            let mut versions = self.model_versions.write().await;
            let versions_entry = versions.entry(model_name).or_insert_with(Vec::new);
            if !versions_entry.contains(&version) {
                versions_entry.push(version);
                versions_entry.sort();
            }
        }

        Ok(())
    }

    pub async fn get_model(&self, model_id: &str) -> Option<AsyncAIModel> {
        let models = self.models.read().await;
        models.get(model_id).cloned()
    }

    pub async fn list_models(&self) -> Vec<ModelInfo> {
        let models = self.models.read().await;
        models.values().map(|model| model.info.clone()).collect()
    }

    pub async fn get_model_versions(&self, model_name: &str) -> Option<Vec<String>> {
        let versions = self.model_versions.read().await;
        versions.get(model_name).cloned()
    }

    pub async fn unregister_model(&self, model_id: &str) -> Result<()> {
        let model_info = {
            let models = self.models.read().await;
            models.get(model_id).map(|model| model.info.clone())
        };

        if let Some(info) = model_info {
            // 移除模型
            {
                let mut models = self.models.write().await;
                models.remove(model_id);
            }

            // 更新版本信息
            {
                let mut versions = self.model_versions.write().await;
                if let Some(versions_list) = versions.get_mut(&info.name) {
                    versions_list.retain(|v| v != &info.version);
                    if versions_list.is_empty() {
                        versions.remove(&info.name);
                    }
                }
            }
        }

        Ok(())
    }
}

/// 流式AI处理器
pub struct StreamingAIProcessor {
    model: AsyncAIModel,
    input_stream: mpsc::UnboundedReceiver<Vec<f32>>,
    output_stream: mpsc::UnboundedSender<InferenceResult>,
}

impl StreamingAIProcessor {
    pub fn new(
        model: AsyncAIModel,
        input_stream: mpsc::UnboundedReceiver<Vec<f32>>,
        output_stream: mpsc::UnboundedSender<InferenceResult>,
    ) -> Self {
        Self {
            model,
            input_stream,
            output_stream,
        }
    }

    pub async fn start_processing(&mut self) -> Result<()> {
        while let Some(input_data) = self.input_stream.recv().await {
            let request = InferenceRequest {
                id: Uuid::new_v4().to_string(),
                model_id: self.model.info.id.clone(),
                input_data,
                priority: InferencePriority::Normal,
                timeout: Duration::from_secs(30),
                metadata: HashMap::new(),
                created_at: Instant::now(),
            };

            match self.model.inference(request).await {
                Ok(result) => {
                    if let Err(e) = self.output_stream.send(result) {
                        println!("      发送结果失败: {}", e);
                        break;
                    }
                }
                Err(e) => {
                    println!("      推理失败: {}", e);
                }
            }
        }

        Ok(())
    }
}

/// 异步AI训练器
#[allow(dead_code)]
pub struct AsyncAITrainer {
    #[allow(dead_code)]
    model_id: String,
    #[allow(dead_code)]
    training_data: Vec<TrainingSample>,
    training_config: TrainingConfig,
    progress_sender: mpsc::UnboundedSender<TrainingProgress>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct TrainingSample {
    pub input: Vec<f32>,
    pub target: Vec<f32>,
    pub weight: f32,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct TrainingConfig {
    pub epochs: u32,
    pub batch_size: usize,
    pub learning_rate: f32,
    pub validation_split: f32,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct TrainingProgress {
    pub epoch: u32,
    pub loss: f32,
    pub accuracy: f32,
    pub validation_loss: f32,
    pub validation_accuracy: f32,
    pub elapsed_time: Duration,
}

#[allow(dead_code)]
impl AsyncAITrainer {
    pub fn new(
        model_id: String,
        training_data: Vec<TrainingSample>,
        training_config: TrainingConfig,
        progress_sender: mpsc::UnboundedSender<TrainingProgress>,
    ) -> Self {
        Self {
            model_id,
            training_data,
            training_config,
            progress_sender,
        }
    }

    pub async fn start_training(&self) -> Result<()> {
        let start_time = Instant::now();
        
        for epoch in 1..=self.training_config.epochs {
            let _epoch_start = Instant::now();
            
            // 模拟训练过程
            let (loss, accuracy) = self.train_epoch(epoch).await?;
            let (validation_loss, validation_accuracy) = self.validate_epoch().await?;
            
            let elapsed_time = start_time.elapsed();
            
            let progress = TrainingProgress {
                epoch,
                loss,
                accuracy,
                validation_loss,
                validation_accuracy,
                elapsed_time,
            };

            if let Err(e) = self.progress_sender.send(progress) {
                println!("      发送训练进度失败: {}", e);
                break;
            }

            println!("      Epoch {}: Loss={:.4}, Accuracy={:.2}%, Val_Loss={:.4}, Val_Accuracy={:.2}%", 
                epoch, loss, accuracy, validation_loss, validation_accuracy);
        }

        Ok(())
    }

    #[allow(dead_code)]
    async fn train_epoch(&self, epoch: u32) -> Result<(f32, f32)> {
        // 模拟训练时间
        let training_time = Duration::from_millis(100 + epoch as u64 * 10);
        sleep(training_time).await;

        // 模拟损失和准确率计算
        let base_loss = 1.0 - (epoch as f32 / self.training_config.epochs as f32) * 0.8;
        let loss = base_loss + rand::random::<f32>() * 0.1;
        let accuracy = (epoch as f32 / self.training_config.epochs as f32) * 90.0 + rand::random::<f32>() * 5.0;

        Ok((loss, accuracy.min(100.0)))
    }

    #[allow(dead_code)]
    async fn validate_epoch(&self) -> Result<(f32, f32)> {
        // 模拟验证时间
        sleep(Duration::from_millis(50)).await;

        // 模拟验证损失和准确率
        let validation_loss = 0.5 + rand::random::<f32>() * 0.2;
        let validation_accuracy = 85.0 + rand::random::<f32>() * 10.0;

        Ok((validation_loss, validation_accuracy.min(100.0)))
    }
}

struct AIIntegrationDemo;

impl AIIntegrationDemo {
    #[allow(dead_code)]
    async fn run() -> Result<()> {
        println!("🤖 AI集成异步演示");
        println!("================================");

        // 1. 异步AI模型推理演示
        println!("\n🧠 1. 异步AI模型推理演示");
        Self::demo_async_inference().await?;

        // 2. 批量推理演示
        println!("\n📦 2. 批量推理演示");
        Self::demo_batch_inference().await?;

        // 3. 流式处理演示
        println!("\n🌊 3. 流式处理演示");
        Self::demo_streaming_processing().await?;

        // 4. 模型管理演示
        println!("\n📋 4. 模型管理演示");
        Self::demo_model_management().await?;

        // 5. 异步训练演示
        println!("\n🏋️ 5. 异步训练演示");
        Self::demo_async_training().await?;

        // 6. AI服务编排演示
        println!("\n🎭 6. AI服务编排演示");
        Self::demo_ai_orchestration().await?;

        Ok(())
    }

    #[allow(dead_code)]
    async fn demo_async_inference() -> Result<()> {
        let model_info = ModelInfo {
            id: "classification-model-1".to_string(),
            name: "ImageClassifier".to_string(),
            version: "1.0.0".to_string(),
            model_type: ModelType::Classification,
            input_shape: vec![224, 224, 3],
            output_shape: vec![10],
            parameters: HashMap::new(),
            created_at: Instant::now(),
            last_updated: Instant::now(),
        };

        let model = AsyncAIModel::new(model_info, 3);

        // 创建推理请求
        let requests = vec![
            InferenceRequest {
                id: Uuid::new_v4().to_string(),
                model_id: model.info.id.clone(),
                input_data: vec![0.1, 0.2, 0.3, 0.4, 0.5],
                priority: InferencePriority::High,
                timeout: Duration::from_secs(30),
                metadata: HashMap::new(),
                created_at: Instant::now(),
            },
            InferenceRequest {
                id: Uuid::new_v4().to_string(),
                model_id: model.info.id.clone(),
                input_data: vec![0.6, 0.7, 0.8, 0.9, 1.0],
                priority: InferencePriority::Normal,
                timeout: Duration::from_secs(30),
                metadata: HashMap::new(),
                created_at: Instant::now(),
            },
        ];

        // 并发推理
        let mut handles = Vec::new();
        for request in requests {
            let model = model.clone();
            let handle = tokio::spawn(async move {
                model.inference(request).await
            });
            handles.push(handle);
        }

        for (i, handle) in handles.into_iter().enumerate() {
            match handle.await? {
                Ok(result) => {
                    println!("      推理请求 {}: 成功", i + 1);
                    println!("        置信度: {:.2}%", result.confidence);
                    println!("        处理时间: {:?}", result.processing_time);
                    println!("        输出维度: {}", result.output_data.len());
                }
                Err(e) => {
                    println!("      推理请求 {}: 失败 - {}", i + 1, e);
                }
            }
        }

        // 显示模型统计
        let stats = model.get_stats().await;
        println!("    模型统计:");
        println!("      队列大小: {}", stats.queue_size);
        println!("      缓存大小: {}", stats.cache_size);
        println!("      可用并发: {}/{}", stats.available_permits, stats.total_permits);

        Ok(())
    }

    #[allow(dead_code)]
    async fn demo_batch_inference() -> Result<()> {
        let model_info = ModelInfo {
            id: "batch-model-1".to_string(),
            name: "BatchProcessor".to_string(),
            version: "1.0.0".to_string(),
            model_type: ModelType::Embedding,
            input_shape: vec![512],
            output_shape: vec![768],
            parameters: HashMap::new(),
            created_at: Instant::now(),
            last_updated: Instant::now(),
        };

        let model = AsyncAIModel::new(model_info, 5);

        // 创建批量请求
        let mut batch_requests = Vec::new();
        for i in 0..10 {
            let request = InferenceRequest {
                id: Uuid::new_v4().to_string(),
                model_id: model.info.id.clone(),
                input_data: vec![i as f32 * 0.1; 512],
                priority: InferencePriority::Normal,
                timeout: Duration::from_secs(30),
                metadata: HashMap::new(),
                created_at: Instant::now(),
            };
            batch_requests.push(request);
        }

        println!("    批量推理 {} 个请求", batch_requests.len());
        let start_time = Instant::now();
        
        let results = model.batch_inference(batch_requests).await?;
        
        let total_time = start_time.elapsed();
        let avg_time = total_time / results.len() as u32;

        println!("    批量推理完成:");
        println!("      总时间: {:?}", total_time);
        println!("      平均时间: {:?}", avg_time);
        println!("      成功数量: {}", results.len());
        println!("      平均置信度: {:.2}%", 
            results.iter().map(|r| r.confidence).sum::<f32>() / results.len() as f32);

        Ok(())
    }

    #[allow(dead_code)]
    #[allow(unused_variables)]
    async fn demo_streaming_processing() -> Result<()> {
        let model_info = ModelInfo {
            id: "streaming-model-1".to_string(),
            name: "StreamProcessor".to_string(),
            version: "1.0.0".to_string(),
            model_type: ModelType::Generation,
            input_shape: vec![256],
            output_shape: vec![512],
            parameters: HashMap::new(),
            created_at: Instant::now(),
            last_updated: Instant::now(),
        };

        let model = AsyncAIModel::new(model_info, 3);

        // 创建输入输出流
        let (input_sender, input_receiver) = mpsc::unbounded_channel();
        let (output_sender, mut output_receiver) = mpsc::unbounded_channel();

        // 创建流式处理器
        let mut processor = StreamingAIProcessor::new(model, input_receiver, output_sender);

        // 启动处理器
        let processor_handle = tokio::spawn(async move {
            processor.start_processing().await
        });

        // 发送输入数据
        println!("    发送流式数据:");
        for i in 0..5 {
            let input_data = vec![i as f32 * 0.2; 256];
            input_sender.send(input_data).unwrap();
            println!("      发送输入批次 {}", i + 1);
            sleep(Duration::from_millis(100)).await;
        }

        // 关闭输入流
        drop(input_sender);

        // 接收输出结果
        println!("    接收流式结果:");
        let mut result_count = 0;
        while let Some(result) = output_receiver.recv().await {
            result_count += 1;
            println!("      接收结果 {}: 置信度 {:.2}%", result_count, result.confidence);
        }

        let _ = processor_handle.await?;

        Ok(())
    }

    #[allow(dead_code)]
    #[allow(unused_variables)]
    async fn demo_model_management() -> Result<()> {
        let manager = AIModelManager::new();

        // 创建多个模型
        let models = vec![
            ModelInfo {
                id: "model-1".to_string(),
                name: "TextClassifier".to_string(),
                version: "1.0.0".to_string(),
                model_type: ModelType::Classification,
                input_shape: vec![512],
                output_shape: vec![5],
                parameters: HashMap::new(),
                created_at: Instant::now(),
                last_updated: Instant::now(),
            },
            ModelInfo {
                id: "model-2".to_string(),
                name: "TextClassifier".to_string(),
                version: "1.1.0".to_string(),
                model_type: ModelType::Classification,
                input_shape: vec![512],
                output_shape: vec![5],
                parameters: HashMap::new(),
                created_at: Instant::now(),
                last_updated: Instant::now(),
            },
            ModelInfo {
                id: "model-3".to_string(),
                name: "ImageGenerator".to_string(),
                version: "2.0.0".to_string(),
                model_type: ModelType::Generation,
                input_shape: vec![256],
                output_shape: vec![1024],
                parameters: HashMap::new(),
                created_at: Instant::now(),
                last_updated: Instant::now(),
            },
        ];

        // 注册模型
        for model_info in models {
            let model = AsyncAIModel::new(model_info.clone(), 2);
            manager.register_model(model).await?;
            println!("    注册模型: {} v{}", model_info.name, model_info.version);
        }

        // 列出所有模型
        let all_models = manager.list_models().await;
        println!("    已注册模型:");
        for model in &all_models {
            println!("      {} v{} ({})", model.name, model.version, model.model_type);
        }

        // 获取模型版本
        let versions = manager.get_model_versions("TextClassifier").await;
        if let Some(versions) = versions {
            println!("    TextClassifier 版本: {:?}", versions);
        }

        // 获取特定模型
        if let Some(model) = manager.get_model("model-1").await {
            let stats = model.get_stats().await;
            println!("    model-1 统计: 可用并发 {}/{}", stats.available_permits, stats.total_permits);
        }

        // 注销模型
        manager.unregister_model("model-2").await?;
        println!("    注销模型: model-2");

        let remaining_models = manager.list_models().await;
        println!("    剩余模型数量: {}", remaining_models.len());

        Ok(())
    }

    #[allow(dead_code)]
    #[allow(unused_variables)]
    async fn demo_async_training() -> Result<()> {
        // 创建训练数据
        let mut training_data = Vec::new();
        for i in 0..1000 {
            training_data.push(TrainingSample {
                input: vec![i as f32 * 0.01; 256],
                target: vec![(i % 10) as f32],
                weight: 1.0,
            });
        }

        let training_config = TrainingConfig {
            epochs: 5,
            batch_size: 32,
            learning_rate: 0.001,
            validation_split: 0.2,
        };

        let (progress_sender, mut progress_receiver) = mpsc::unbounded_channel();

        let trainer = AsyncAITrainer::new(
            "training-model-1".to_string(),
            training_data,
            training_config,
            progress_sender,
        );

        // 启动训练
        let trainer_handle = tokio::spawn(async move {
            trainer.start_training().await
        });

        // 监控训练进度
        let mut progress_count = 0;
        while let Some(progress) = progress_receiver.recv().await {
            progress_count += 1;
            if progress_count % 2 == 0 { // 每2个epoch显示一次
                println!("      Epoch {}: Loss={:.4}, Acc={:.1}%, Val_Loss={:.4}, Val_Acc={:.1}%", 
                    progress.epoch, progress.loss, progress.accuracy, 
                    progress.validation_loss, progress.validation_accuracy);
            }
        }

        let _ = trainer_handle.await?;

        Ok(())
    }

    #[allow(dead_code)]
    #[allow(unused_variables)]
    async fn demo_ai_orchestration() -> Result<()> {
        println!("    创建AI服务编排工作流");

        // 创建多个AI服务
        let text_classifier = AsyncAIModel::new(ModelInfo {
            id: "text-classifier".to_string(),
            name: "TextClassifier".to_string(),
            version: "1.0.0".to_string(),
            model_type: ModelType::Classification,
            input_shape: vec![512],
            output_shape: vec![5],
            parameters: HashMap::new(),
            created_at: Instant::now(),
            last_updated: Instant::now(),
        }, 2);

        let text_generator = AsyncAIModel::new(ModelInfo {
            id: "text-generator".to_string(),
            name: "TextGenerator".to_string(),
            version: "1.0.0".to_string(),
            model_type: ModelType::Generation,
            input_shape: vec![256],
            output_shape: vec![512],
            parameters: HashMap::new(),
            created_at: Instant::now(),
            last_updated: Instant::now(),
        }, 2);

        // 模拟AI服务编排工作流
        let input_text = vec![0.1; 256];
        
        // 步骤1: 文本分类
        let classification_request = InferenceRequest {
            id: Uuid::new_v4().to_string(),
            model_id: text_classifier.info.id.clone(),
            input_data: input_text.clone(),
            priority: InferencePriority::High,
            timeout: Duration::from_secs(30),
            metadata: HashMap::new(),
            created_at: Instant::now(),
        };

        let classification_result = text_classifier.inference(classification_request).await?;
        println!("      步骤1 - 文本分类: 置信度 {:.2}%", classification_result.confidence);

        // 步骤2: 基于分类结果生成文本
        let generation_input = classification_result.output_data[..256.min(classification_result.output_data.len())].to_vec();
        let generation_request = InferenceRequest {
            id: Uuid::new_v4().to_string(),
            model_id: text_generator.info.id.clone(),
            input_data: generation_input,
            priority: InferencePriority::Normal,
            timeout: Duration::from_secs(30),
            metadata: HashMap::new(),
            created_at: Instant::now(),
        };

        let generation_result = text_generator.inference(generation_request).await?;
        println!("      步骤2 - 文本生成: 置信度 {:.2}%", generation_result.confidence);

        // 步骤3: 并行后处理
        let post_processing_handles = vec![
            tokio::spawn(async {
                sleep(Duration::from_millis(50)).await;
                "后处理任务1完成".to_string()
            }),
            tokio::spawn(async {
                sleep(Duration::from_millis(75)).await;
                "后处理任务2完成".to_string()
            }),
            tokio::spawn(async {
                sleep(Duration::from_millis(60)).await;
                "后处理任务3完成".to_string()
            }),
        ];

        for (i, handle) in post_processing_handles.into_iter().enumerate() {
            let result = handle.await?;
            println!("      步骤3.{} - 并行后处理: {}", i + 1, result);
        }

        println!("    AI服务编排工作流完成");

        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    AIIntegrationDemo::run().await?;

    println!("\n🎉 AI集成异步演示完成！");
    Ok(())
}
