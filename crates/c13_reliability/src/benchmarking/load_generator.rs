/// 负载生成器
///
/// 用于生成各种负载模式，用于性能测试和压力测试

use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::Semaphore;
use tokio::time::sleep;

use crate::prelude::*;

/// 负载模式
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoadPattern {
    /// 恒定负载 - 保持固定的请求速率
    Constant,
    /// 线性增长 - 请求速率线性增加
    Linear,
    /// 阶梯增长 - 请求速率阶梯式增加
    Step,
    /// 峰值负载 - 突发峰值
    Spike,
    /// 正弦波负载 - 周期性波动
    Sine,
}

/// 负载生成器配置
#[derive(Debug, Clone)]
pub struct LoadConfig {
    /// 初始请求速率（每秒）
    pub initial_rate: f64,
    /// 最大请求速率（每秒）
    pub max_rate: f64,
    /// 测试持续时间
    pub duration: Duration,
    /// 负载模式
    pub pattern: LoadPattern,
    /// 最大并发数
    pub max_concurrency: usize,
}

impl Default for LoadConfig {
    fn default() -> Self {
        Self {
            initial_rate: 10.0,
            max_rate: 100.0,
            duration: Duration::from_secs(60),
            pattern: LoadPattern::Constant,
            max_concurrency: 100,
        }
    }
}

/// 负载生成器
pub struct LoadGenerator {
    config: LoadConfig,
    semaphore: Arc<Semaphore>,
}

impl LoadGenerator {
    /// 创建新的负载生成器
    pub fn new(config: LoadConfig) -> Self {
        let semaphore = Arc::new(Semaphore::new(config.max_concurrency));
        Self { config, semaphore }
    }

    /// 生成负载
    ///
    /// 使用提供的任务函数生成负载，并返回执行结果
    pub async fn generate<F, Fut, T>(&self, task: F) -> Result<LoadResults<T>>
    where
        F: Fn() -> Fut + Send + Sync + 'static,
        Fut: std::future::Future<Output = Result<T>> + Send,
        T: Send + 'static,
    {
        let task = Arc::new(task);
        let start_time = Instant::now();
        let mut results = Vec::new();
        let mut request_count = 0;

        while start_time.elapsed() < self.config.duration {
            let elapsed = start_time.elapsed();
            let rate = self.calculate_rate(elapsed);
            let interval = Duration::from_secs_f64(1.0 / rate);

            // 获取信号量许可
            let permit = self.semaphore.clone().acquire_owned().await;
            if permit.is_err() {
                break;
            }
            let permit = permit.unwrap();

            let task_clone = Arc::clone(&task);
            let request_start = Instant::now();

            // 异步执行任务
            let handle = tokio::spawn(async move {
                let result = task_clone().await;
                let latency = request_start.elapsed();
                drop(permit);
                (result, latency)
            });

            results.push(handle);
            request_count += 1;

            // 等待下一个请求
            sleep(interval).await;
        }

        // 收集所有结果
        let mut successful = 0;
        let mut failed = 0;
        let mut latencies = Vec::new();
        let mut errors = Vec::new();

        for result in results {
            match result.await {
                Ok((Ok(_), latency)) => {
                    successful += 1;
                    latencies.push(latency);
                }
                Ok((Err(e), latency)) => {
                    failed += 1;
                    latencies.push(latency);
                    errors.push(e.to_string());
                }
                Err(e) => {
                    failed += 1;
                    errors.push(e.to_string());
                }
            }
        }

        Ok(LoadResults {
            total_requests: request_count,
            successful_requests: successful,
            failed_requests: failed,
            duration: start_time.elapsed(),
            latencies,
            errors,
            _phantom: std::marker::PhantomData,
        })
    }

    /// 根据负载模式计算当前请求速率
    fn calculate_rate(&self, elapsed: Duration) -> f64 {
        let progress = elapsed.as_secs_f64() / self.config.duration.as_secs_f64();
        let progress = progress.min(1.0);

        match self.config.pattern {
            LoadPattern::Constant => self.config.initial_rate,
            LoadPattern::Linear => {
                self.config.initial_rate
                    + (self.config.max_rate - self.config.initial_rate) * progress
            }
            LoadPattern::Step => {
                let step = (progress * 10.0).floor() / 10.0;
                self.config.initial_rate
                    + (self.config.max_rate - self.config.initial_rate) * step
            }
            LoadPattern::Spike => {
                if progress > 0.4 && progress < 0.6 {
                    self.config.max_rate
                } else {
                    self.config.initial_rate
                }
            }
            LoadPattern::Sine => {
                let amplitude = (self.config.max_rate - self.config.initial_rate) / 2.0;
                let offset = self.config.initial_rate + amplitude;
                offset + amplitude * (progress * 2.0 * std::f64::consts::PI).sin()
            }
        }
    }
}

/// 负载测试结果
#[derive(Debug)]
pub struct LoadResults<T> {
    /// 总请求数
    pub total_requests: usize,
    /// 成功请求数
    pub successful_requests: usize,
    /// 失败请求数
    pub failed_requests: usize,
    /// 测试持续时间
    pub duration: Duration,
    /// 延迟列表
    pub latencies: Vec<Duration>,
    /// 错误列表
    pub errors: Vec<String>,
    /// 防止未使用泛型警告
    _phantom: std::marker::PhantomData<T>,
}

impl<T> LoadResults<T> {
    /// 获取成功率
    pub fn success_rate(&self) -> f64 {
        if self.total_requests == 0 {
            return 0.0;
        }
        self.successful_requests as f64 / self.total_requests as f64
    }

    /// 获取平均延迟
    pub fn average_latency(&self) -> Duration {
        if self.latencies.is_empty() {
            return Duration::ZERO;
        }
        let total: Duration = self.latencies.iter().sum();
        total / self.latencies.len() as u32
    }

    /// 获取吞吐量（每秒请求数）
    pub fn throughput(&self) -> f64 {
        if self.duration.as_secs_f64() == 0.0 {
            return 0.0;
        }
        self.successful_requests as f64 / self.duration.as_secs_f64()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_constant_load() {
        let config = LoadConfig {
            initial_rate: 10.0,
            max_rate: 10.0,
            duration: Duration::from_secs(1),
            pattern: LoadPattern::Constant,
            max_concurrency: 10,
        };

        let generator = LoadGenerator::new(config);

        let results: LoadResults<()> = generator
            .generate(|| async {
                sleep(Duration::from_millis(10)).await;
                Ok(())
            })
            .await
            .unwrap();

        assert!(results.total_requests > 0);
        assert_eq!(results.failed_requests, 0);
    }

    #[tokio::test]
    async fn test_linear_load() {
        let config = LoadConfig {
            initial_rate: 5.0,
            max_rate: 20.0,
            duration: Duration::from_secs(2),
            pattern: LoadPattern::Linear,
            max_concurrency: 50,
        };

        let generator = LoadGenerator::new(config);

        let results: LoadResults<()> = generator
            .generate(|| async {
                sleep(Duration::from_millis(5)).await;
                Ok(())
            })
            .await
            .unwrap();

        assert!(results.total_requests > 10);
        assert!(results.success_rate() > 0.9);
    }
}

