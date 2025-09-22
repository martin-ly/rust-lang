//! 训练管道
//! 
//! 提供完整的模型训练管道实现

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;
use uuid::Uuid;
use chrono::{DateTime, Utc};
use tokio::sync::mpsc;
// use tokio::time::{Duration, Instant};

use crate::model_management::{ModelRegistry, ModelType, Framework};
use super::job::TrainingJob;
use super::metrics::TrainingMetrics;
use super::checkpoint::CheckpointManager;

/// 训练管道
#[derive(Debug, Clone)]
pub struct TrainingPipeline {
    pub id: String,
    pub name: String,
    pub config: TrainingConfig,
    pub status: PipelineStatus,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 训练配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrainingConfig {
    pub model_config: ModelTrainingConfig,
    pub data_config: DataConfig,
    pub optimizer_config: OptimizerConfig,
    pub scheduler_config: SchedulerConfig,
    pub checkpoint_config: CheckpointConfig,
    pub validation_config: ValidationConfig,
}

/// 模型训练配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelTrainingConfig {
    pub model_type: ModelType,
    pub framework: Framework,
    pub architecture: String,
    pub input_shape: Vec<usize>,
    pub output_shape: Vec<usize>,
    pub parameters: HashMap<String, serde_json::Value>,
}

/// 数据配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataConfig {
    pub train_dataset_path: PathBuf,
    pub validation_dataset_path: Option<PathBuf>,
    pub test_dataset_path: Option<PathBuf>,
    pub batch_size: usize,
    pub num_workers: usize,
    pub shuffle: bool,
    pub data_augmentation: Option<DataAugmentationConfig>,
}

/// 数据增强配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataAugmentationConfig {
    pub rotation: Option<f32>,
    pub flip_horizontal: bool,
    pub flip_vertical: bool,
    pub brightness: Option<f32>,
    pub contrast: Option<f32>,
    pub noise: Option<f32>,
}

/// 优化器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OptimizerConfig {
    pub optimizer_type: OptimizerType,
    pub learning_rate: f64,
    pub weight_decay: Option<f64>,
    pub momentum: Option<f64>,
    pub beta1: Option<f64>,
    pub beta2: Option<f64>,
    pub epsilon: Option<f64>,
}

/// 优化器类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OptimizerType {
    SGD,
    Adam,
    AdamW,
    RMSprop,
    Adagrad,
    Adadelta,
}

/// 学习率调度器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchedulerConfig {
    pub scheduler_type: SchedulerType,
    pub step_size: Option<usize>,
    pub gamma: Option<f64>,
    pub milestones: Option<Vec<usize>>,
    pub patience: Option<usize>,
    pub factor: Option<f64>,
    pub min_lr: Option<f64>,
}

/// 调度器类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SchedulerType {
    StepLR,
    MultiStepLR,
    ExponentialLR,
    CosineAnnealingLR,
    ReduceLROnPlateau,
    OneCycleLR,
}

/// 检查点配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckpointConfig {
    pub save_interval: usize, // epochs
    pub save_best: bool,
    pub save_last: bool,
    pub max_checkpoints: usize,
    pub checkpoint_dir: PathBuf,
}

/// 验证配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationConfig {
    pub validation_interval: usize, // epochs
    pub early_stopping: Option<EarlyStoppingConfig>,
    pub metrics: Vec<String>,
}

/// 早停配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EarlyStoppingConfig {
    pub patience: usize,
    pub min_delta: f64,
    pub monitor: String,
    pub mode: EarlyStoppingMode,
}

/// 早停模式
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EarlyStoppingMode {
    Min,
    Max,
}

/// 管道状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PipelineStatus {
    Created,
    Running,
    Paused,
    Completed,
    Failed,
    Cancelled,
}

/// 训练管道管理器
#[derive(Debug)]
pub struct TrainingPipelineManager {
    pipelines: HashMap<String, TrainingPipeline>,
    jobs: HashMap<String, TrainingJob>,
    model_registry: ModelRegistry,
    checkpoint_manager: CheckpointManager,
    metrics_collector: TrainingMetrics,
    job_sender: mpsc::UnboundedSender<TrainingJob>,
}

impl TrainingPipelineManager {
    /// 创建新的训练管道管理器
    pub fn new(
        model_registry: ModelRegistry,
        checkpoint_manager: CheckpointManager,
    ) -> (Self, mpsc::UnboundedReceiver<TrainingJob>) {
        let (job_sender, job_receiver) = mpsc::unbounded_channel();
        
        let manager = Self {
            pipelines: HashMap::new(),
            jobs: HashMap::new(),
            model_registry,
            checkpoint_manager,
            metrics_collector: TrainingMetrics::new("pipeline".to_string()),
            job_sender,
        };

        (manager, job_receiver)
    }

    /// 创建训练管道
    pub async fn create_pipeline(
        &mut self,
        name: String,
        config: TrainingConfig,
    ) -> Result<TrainingPipeline> {
        let pipeline_id = Uuid::new_v4().to_string();
        let now = Utc::now();

        let pipeline = TrainingPipeline {
            id: pipeline_id.clone(),
            name,
            config,
            status: PipelineStatus::Created,
            created_at: now,
            updated_at: now,
        };

        self.pipelines.insert(pipeline_id.clone(), pipeline.clone());
        Ok(pipeline)
    }

    /// 启动训练管道
    pub async fn start_pipeline(&mut self, pipeline_id: &str) -> Result<TrainingJob> {
        let pipeline = self.pipelines.get_mut(pipeline_id)
            .ok_or_else(|| anyhow::anyhow!("Pipeline not found: {}", pipeline_id))?;

        if !matches!(pipeline.status, PipelineStatus::Created) {
            return Err(anyhow::anyhow!("Pipeline is not in created state"));
        }

        // 创建训练任务
        let job = TrainingJob::new(
            pipeline_id.to_string(),
            pipeline.config.clone(),
        );

        // 更新管道状态
        pipeline.status = PipelineStatus::Running;
        pipeline.updated_at = Utc::now();

        // 保存任务
        self.jobs.insert(job.id.clone(), job.clone());

        // 发送任务到执行队列
        self.job_sender.send(job.clone())?;

        Ok(job)
    }

    /// 暂停训练管道
    pub async fn pause_pipeline(&mut self, pipeline_id: &str) -> Result<()> {
        let pipeline = self.pipelines.get_mut(pipeline_id)
            .ok_or_else(|| anyhow::anyhow!("Pipeline not found: {}", pipeline_id))?;

        if !matches!(pipeline.status, PipelineStatus::Running) {
            return Err(anyhow::anyhow!("Pipeline is not running"));
        }

        pipeline.status = PipelineStatus::Paused;
        pipeline.updated_at = Utc::now();

        // 暂停相关的训练任务
        if let Some(job) = self.jobs.get_mut(pipeline_id) {
            job.pause().await?;
        }

        Ok(())
    }

    /// 恢复训练管道
    pub async fn resume_pipeline(&mut self, pipeline_id: &str) -> Result<()> {
        let pipeline = self.pipelines.get_mut(pipeline_id)
            .ok_or_else(|| anyhow::anyhow!("Pipeline not found: {}", pipeline_id))?;

        if !matches!(pipeline.status, PipelineStatus::Paused) {
            return Err(anyhow::anyhow!("Pipeline is not paused"));
        }

        pipeline.status = PipelineStatus::Running;
        pipeline.updated_at = Utc::now();

        // 恢复相关的训练任务
        if let Some(job) = self.jobs.get_mut(pipeline_id) {
            job.resume().await?;
        }

        Ok(())
    }

    /// 取消训练管道
    pub async fn cancel_pipeline(&mut self, pipeline_id: &str) -> Result<()> {
        let pipeline = self.pipelines.get_mut(pipeline_id)
            .ok_or_else(|| anyhow::anyhow!("Pipeline not found: {}", pipeline_id))?;

        pipeline.status = PipelineStatus::Cancelled;
        pipeline.updated_at = Utc::now();

        // 取消相关的训练任务
        if let Some(job) = self.jobs.get_mut(pipeline_id) {
            job.cancel().await?;
        }

        Ok(())
    }

    /// 获取管道状态
    pub fn get_pipeline_status(&self, pipeline_id: &str) -> Option<&PipelineStatus> {
        self.pipelines.get(pipeline_id).map(|p| &p.status)
    }

    /// 获取训练任务
    pub fn get_training_job(&self, job_id: &str) -> Option<&TrainingJob> {
        self.jobs.get(job_id)
    }

    /// 获取所有管道
    pub fn get_all_pipelines(&self) -> Vec<&TrainingPipeline> {
        self.pipelines.values().collect()
    }

    /// 获取所有训练任务
    pub fn get_all_jobs(&self) -> Vec<&TrainingJob> {
        self.jobs.values().collect()
    }

    /// 更新任务状态
    pub async fn update_job_status(&mut self, job_id: &str, status: super::job::JobStatus) -> Result<()> {
        if let Some(job) = self.jobs.get_mut(job_id) {
            job.update_status(status).await?;
        }
        Ok(())
    }

    /// 获取训练指标
    pub fn get_training_metrics(&self, job_id: &str) -> Option<&TrainingMetrics> {
        self.jobs.get(job_id).map(|_| &self.metrics_collector)
    }

    /// 保存检查点
    pub async fn save_checkpoint(&mut self, job_id: &str, epoch: usize) -> Result<()> {
        if let Some(job) = self.jobs.get(job_id) {
            self.checkpoint_manager.save_checkpoint(job, epoch.try_into().unwrap()).await?;
        }
        Ok(())
    }

    /// 加载检查点
    pub async fn load_checkpoint(&mut self, job_id: &str, checkpoint_path: &PathBuf) -> Result<()> {
        if let Some(job) = self.jobs.get_mut(job_id) {
            self.checkpoint_manager.load_checkpoint(job, checkpoint_path.to_str().unwrap()).await?;
        }
        Ok(())
    }

    /// 获取管道统计信息
    pub fn get_pipeline_statistics(&self) -> PipelineStatistics {
        let mut stats = PipelineStatistics::default();

        for pipeline in self.pipelines.values() {
            stats.total_pipelines += 1;

            match pipeline.status {
                PipelineStatus::Created => stats.created_pipelines += 1,
                PipelineStatus::Running => stats.running_pipelines += 1,
                PipelineStatus::Paused => stats.paused_pipelines += 1,
                PipelineStatus::Completed => stats.completed_pipelines += 1,
                PipelineStatus::Failed => stats.failed_pipelines += 1,
                PipelineStatus::Cancelled => stats.cancelled_pipelines += 1,
            }
        }

        for job in self.jobs.values() {
            stats.total_jobs += 1;
            stats.total_training_time += job.get_training_time().as_secs();
        }

        stats
    }
}

/// 管道统计信息
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct PipelineStatistics {
    pub total_pipelines: u32,
    pub created_pipelines: u32,
    pub running_pipelines: u32,
    pub paused_pipelines: u32,
    pub completed_pipelines: u32,
    pub failed_pipelines: u32,
    pub cancelled_pipelines: u32,
    pub total_jobs: u32,
    pub total_training_time: u64,
}
