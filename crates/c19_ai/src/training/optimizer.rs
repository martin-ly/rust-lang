//! 训练优化器
//! 
//! 提供各种优化算法和调度器

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;
use chrono::{DateTime, Utc};

/// 优化器
#[derive(Debug, Clone)]
pub struct Optimizer {
    pub id: Uuid,
    pub name: String,
    pub optimizer_type: OptimizerType,
    pub parameters: OptimizerParameters,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 优化器类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OptimizerType {
    /// 随机梯度下降
    SGD,
    /// Adam优化器
    Adam,
    /// AdamW优化器
    AdamW,
    /// RMSprop优化器
    RMSprop,
    /// AdaGrad优化器
    AdaGrad,
    /// AdaDelta优化器
    AdaDelta,
    /// 动量优化器
    Momentum,
    /// Nesterov动量优化器
    NesterovMomentum,
    /// 自定义优化器
    Custom(String),
}

/// 优化器参数
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OptimizerParameters {
    pub learning_rate: f64,
    pub weight_decay: Option<f64>,
    pub momentum: Option<f64>,
    pub beta1: Option<f64>,
    pub beta2: Option<f64>,
    pub epsilon: Option<f64>,
    pub rho: Option<f64>,
    pub alpha: Option<f64>,
    pub custom_parameters: HashMap<String, f64>,
}

/// 学习率调度器
#[derive(Debug, Clone)]
pub struct LearningRateScheduler {
    pub id: Uuid,
    pub name: String,
    pub scheduler_type: SchedulerType,
    pub parameters: SchedulerParameters,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 调度器类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SchedulerType {
    /// 固定学习率
    Constant,
    /// 线性衰减
    Linear,
    /// 指数衰减
    Exponential,
    /// 余弦退火
    CosineAnnealing,
    /// 步长衰减
    Step,
    /// 多步衰减
    MultiStep,
    /// 多项式衰减
    Polynomial,
    /// 循环学习率
    Cyclic,
    /// 自定义调度器
    Custom(String),
}

/// 调度器参数
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchedulerParameters {
    pub initial_lr: f64,
    pub final_lr: Option<f64>,
    pub step_size: Option<usize>,
    pub gamma: Option<f64>,
    pub milestones: Option<Vec<usize>>,
    pub power: Option<f64>,
    pub max_lr: Option<f64>,
    pub base_lr: Option<f64>,
    pub step_size_up: Option<usize>,
    pub step_size_down: Option<usize>,
    pub mode: Option<SchedulerMode>,
    pub custom_parameters: HashMap<String, f64>,
}

/// 调度器模式
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SchedulerMode {
    Min,
    Max,
}

/// 优化器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OptimizerConfig {
    pub optimizer: OptimizerType,
    pub scheduler: Option<SchedulerType>,
    pub parameters: OptimizerParameters,
    pub scheduler_parameters: Option<SchedulerParameters>,
    pub gradient_clipping: Option<GradientClipping>,
    pub early_stopping: Option<EarlyStopping>,
}

/// 梯度裁剪
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GradientClipping {
    pub clipping_type: ClippingType,
    pub value: f64,
}

/// 裁剪类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ClippingType {
    Norm,
    Value,
}

/// 早停策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EarlyStopping {
    pub patience: usize,
    pub min_delta: f64,
    pub monitor: String,
    pub mode: EarlyStoppingMode,
    pub restore_best_weights: bool,
}

/// 早停模式
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EarlyStoppingMode {
    Min,
    Max,
}

/// 优化器工厂
pub struct OptimizerFactory;

impl OptimizerFactory {
    /// 创建SGD优化器
    pub fn create_sgd(learning_rate: f64, momentum: Option<f64>, weight_decay: Option<f64>) -> Optimizer {
        Optimizer {
            id: Uuid::new_v4(),
            name: "SGD".to_string(),
            optimizer_type: OptimizerType::SGD,
            parameters: OptimizerParameters {
                learning_rate,
                weight_decay,
                momentum,
                beta1: None,
                beta2: None,
                epsilon: None,
                rho: None,
                alpha: None,
                custom_parameters: HashMap::new(),
            },
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 创建Adam优化器
    pub fn create_adam(learning_rate: f64, beta1: f64, beta2: f64, epsilon: f64, weight_decay: Option<f64>) -> Optimizer {
        Optimizer {
            id: Uuid::new_v4(),
            name: "Adam".to_string(),
            optimizer_type: OptimizerType::Adam,
            parameters: OptimizerParameters {
                learning_rate,
                weight_decay,
                momentum: None,
                beta1: Some(beta1),
                beta2: Some(beta2),
                epsilon: Some(epsilon),
                rho: None,
                alpha: None,
                custom_parameters: HashMap::new(),
            },
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 创建AdamW优化器
    pub fn create_adamw(learning_rate: f64, beta1: f64, beta2: f64, epsilon: f64, weight_decay: f64) -> Optimizer {
        Optimizer {
            id: Uuid::new_v4(),
            name: "AdamW".to_string(),
            optimizer_type: OptimizerType::AdamW,
            parameters: OptimizerParameters {
                learning_rate,
                weight_decay: Some(weight_decay),
                momentum: None,
                beta1: Some(beta1),
                beta2: Some(beta2),
                epsilon: Some(epsilon),
                rho: None,
                alpha: None,
                custom_parameters: HashMap::new(),
            },
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 创建RMSprop优化器
    pub fn create_rmsprop(learning_rate: f64, alpha: f64, epsilon: f64, weight_decay: Option<f64>) -> Optimizer {
        Optimizer {
            id: Uuid::new_v4(),
            name: "RMSprop".to_string(),
            optimizer_type: OptimizerType::RMSprop,
            parameters: OptimizerParameters {
                learning_rate,
                weight_decay,
                momentum: None,
                beta1: None,
                beta2: None,
                epsilon: Some(epsilon),
                rho: None,
                alpha: Some(alpha),
                custom_parameters: HashMap::new(),
            },
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }
}

/// 学习率调度器工厂
pub struct SchedulerFactory;

impl SchedulerFactory {
    /// 创建固定学习率调度器
    pub fn create_constant(initial_lr: f64) -> LearningRateScheduler {
        LearningRateScheduler {
            id: Uuid::new_v4(),
            name: "Constant".to_string(),
            scheduler_type: SchedulerType::Constant,
            parameters: SchedulerParameters {
                initial_lr,
                final_lr: None,
                step_size: None,
                gamma: None,
                milestones: None,
                power: None,
                max_lr: None,
                base_lr: None,
                step_size_up: None,
                step_size_down: None,
                mode: None,
                custom_parameters: HashMap::new(),
            },
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 创建线性衰减调度器
    pub fn create_linear(initial_lr: f64, final_lr: f64) -> LearningRateScheduler {
        LearningRateScheduler {
            id: Uuid::new_v4(),
            name: "Linear".to_string(),
            scheduler_type: SchedulerType::Linear,
            parameters: SchedulerParameters {
                initial_lr,
                final_lr: Some(final_lr),
                step_size: None,
                gamma: None,
                milestones: None,
                power: None,
                max_lr: None,
                base_lr: None,
                step_size_up: None,
                step_size_down: None,
                mode: None,
                custom_parameters: HashMap::new(),
            },
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 创建指数衰减调度器
    pub fn create_exponential(initial_lr: f64, gamma: f64) -> LearningRateScheduler {
        LearningRateScheduler {
            id: Uuid::new_v4(),
            name: "Exponential".to_string(),
            scheduler_type: SchedulerType::Exponential,
            parameters: SchedulerParameters {
                initial_lr,
                final_lr: None,
                step_size: None,
                gamma: Some(gamma),
                milestones: None,
                power: None,
                max_lr: None,
                base_lr: None,
                step_size_up: None,
                step_size_down: None,
                mode: None,
                custom_parameters: HashMap::new(),
            },
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 创建步长衰减调度器
    pub fn create_step(initial_lr: f64, step_size: usize, gamma: f64) -> LearningRateScheduler {
        LearningRateScheduler {
            id: Uuid::new_v4(),
            name: "Step".to_string(),
            scheduler_type: SchedulerType::Step,
            parameters: SchedulerParameters {
                initial_lr,
                final_lr: None,
                step_size: Some(step_size),
                gamma: Some(gamma),
                milestones: None,
                power: None,
                max_lr: None,
                base_lr: None,
                step_size_up: None,
                step_size_down: None,
                mode: None,
                custom_parameters: HashMap::new(),
            },
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 创建多步衰减调度器
    pub fn create_multistep(initial_lr: f64, milestones: Vec<usize>, gamma: f64) -> LearningRateScheduler {
        LearningRateScheduler {
            id: Uuid::new_v4(),
            name: "MultiStep".to_string(),
            scheduler_type: SchedulerType::MultiStep,
            parameters: SchedulerParameters {
                initial_lr,
                final_lr: None,
                step_size: None,
                gamma: Some(gamma),
                milestones: Some(milestones),
                power: None,
                max_lr: None,
                base_lr: None,
                step_size_up: None,
                step_size_down: None,
                mode: None,
                custom_parameters: HashMap::new(),
            },
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 创建余弦退火调度器
    pub fn create_cosine_annealing(initial_lr: f64, final_lr: f64) -> LearningRateScheduler {
        LearningRateScheduler {
            id: Uuid::new_v4(),
            name: "CosineAnnealing".to_string(),
            scheduler_type: SchedulerType::CosineAnnealing,
            parameters: SchedulerParameters {
                initial_lr,
                final_lr: Some(final_lr),
                step_size: None,
                gamma: None,
                milestones: None,
                power: None,
                max_lr: None,
                base_lr: None,
                step_size_up: None,
                step_size_down: None,
                mode: None,
                custom_parameters: HashMap::new(),
            },
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }
}

/// 优化器管理器
#[derive(Debug)]
pub struct OptimizerManager {
    optimizers: HashMap<String, Optimizer>,
    schedulers: HashMap<String, LearningRateScheduler>,
    configs: HashMap<String, OptimizerConfig>,
}

impl OptimizerManager {
    /// 创建新的优化器管理器
    pub fn new() -> Self {
        Self {
            optimizers: HashMap::new(),
            schedulers: HashMap::new(),
            configs: HashMap::new(),
        }
    }

    /// 注册优化器
    pub fn register_optimizer(&mut self, name: String, optimizer: Optimizer) {
        self.optimizers.insert(name, optimizer);
    }

    /// 注册调度器
    pub fn register_scheduler(&mut self, name: String, scheduler: LearningRateScheduler) {
        self.schedulers.insert(name, scheduler);
    }

    /// 注册优化器配置
    pub fn register_config(&mut self, name: String, config: OptimizerConfig) {
        self.configs.insert(name, config);
    }

    /// 获取优化器
    pub fn get_optimizer(&self, name: &str) -> Option<&Optimizer> {
        self.optimizers.get(name)
    }

    /// 获取调度器
    pub fn get_scheduler(&self, name: &str) -> Option<&LearningRateScheduler> {
        self.schedulers.get(name)
    }

    /// 获取配置
    pub fn get_config(&self, name: &str) -> Option<&OptimizerConfig> {
        self.configs.get(name)
    }

    /// 创建预定义配置
    pub fn create_preset_configs(&mut self) {
        // SGD配置
        let sgd_config = OptimizerConfig {
            optimizer: OptimizerType::SGD,
            scheduler: Some(SchedulerType::Step),
            parameters: OptimizerParameters {
                learning_rate: 0.01,
                weight_decay: Some(1e-4),
                momentum: Some(0.9),
                beta1: None,
                beta2: None,
                epsilon: None,
                rho: None,
                alpha: None,
                custom_parameters: HashMap::new(),
            },
            scheduler_parameters: Some(SchedulerParameters {
                initial_lr: 0.01,
                final_lr: None,
                step_size: Some(30),
                gamma: Some(0.1),
                milestones: None,
                power: None,
                max_lr: None,
                base_lr: None,
                step_size_up: None,
                step_size_down: None,
                mode: None,
                custom_parameters: HashMap::new(),
            }),
            gradient_clipping: Some(GradientClipping {
                clipping_type: ClippingType::Norm,
                value: 1.0,
            }),
            early_stopping: Some(EarlyStopping {
                patience: 10,
                min_delta: 1e-4,
                monitor: "val_loss".to_string(),
                mode: EarlyStoppingMode::Min,
                restore_best_weights: true,
            }),
        };

        // Adam配置
        let adam_config = OptimizerConfig {
            optimizer: OptimizerType::Adam,
            scheduler: Some(SchedulerType::CosineAnnealing),
            parameters: OptimizerParameters {
                learning_rate: 0.001,
                weight_decay: Some(1e-4),
                momentum: None,
                beta1: Some(0.9),
                beta2: Some(0.999),
                epsilon: Some(1e-8),
                rho: None,
                alpha: None,
                custom_parameters: HashMap::new(),
            },
            scheduler_parameters: Some(SchedulerParameters {
                initial_lr: 0.001,
                final_lr: Some(1e-6),
                step_size: None,
                gamma: None,
                milestones: None,
                power: None,
                max_lr: None,
                base_lr: None,
                step_size_up: None,
                step_size_down: None,
                mode: None,
                custom_parameters: HashMap::new(),
            }),
            gradient_clipping: Some(GradientClipping {
                clipping_type: ClippingType::Norm,
                value: 1.0,
            }),
            early_stopping: Some(EarlyStopping {
                patience: 15,
                min_delta: 1e-4,
                monitor: "val_loss".to_string(),
                mode: EarlyStoppingMode::Min,
                restore_best_weights: true,
            }),
        };

        self.register_config("sgd_default".to_string(), sgd_config);
        self.register_config("adam_default".to_string(), adam_config);
    }
}

impl Default for OptimizerManager {
    fn default() -> Self {
        Self::new()
    }
}
