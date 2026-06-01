//! 指数退避重试策略（替代已废弃的 backoff crate）
//! index strategy （ backoff crate）
//!
//! 提供与 backoff 0.4.x 兼容的 `ExponentialBackoff` API，
//! 以及一个简化的异步重试助手函数。
//! and async function 。
use std::time::{Duration, Instant};

/// 指数退避配置
/// index
#[derive(Debug, Clone)]
pub struct ExponentialBackoff {
    /// 初始重试间隔
    pub initial_interval: Duration,
    /// 最大重试间隔
    /// maximum
    pub max_interval: Duration,
    /// 最大累计重试时间（None 表示无限制）
    /// maximum time （None represent ）
    pub max_elapsed_time: Option<Duration>,
    /// 间隔乘数
    pub multiplier: f64,
    /// 随机化因子（0.0~1.0），为 0 时不添加 jitter
    /// factor （0.0~1.0），as 0 jitter
    pub randomization_factor: f64,
    /// 当前间隔（内部状态，由 next_backoff 维护）
    /// when before （inside state ， next_backoff ）
    pub current_interval: Duration,
    /// 开始时间（内部状态，由 next_backoff 维护）
    /// Start timeinternalstatus next_backoff
    pub start_time: Option<Instant>,
}

impl Default for ExponentialBackoff {
    fn default() -> Self {
        Self {
            initial_interval: Duration::from_millis(500),
            max_interval: Duration::from_secs(60),
            max_elapsed_time: Some(Duration::from_secs(15 * 60)),
            multiplier: 1.5,
            randomization_factor: 0.5,
            current_interval: Duration::from_millis(500),
            start_time: None,
        }
    }
}

impl ExponentialBackoff {
    /// 计算下一次退避延迟
    /// Compute lower
    pub fn next_backoff(&mut self) -> Option<Duration> {
        if self.start_time.is_none() {
            self.start_time = Some(Instant::now());
        }

        // 检查是否超过最大累计时间
        if let Some(max_elapsed) = self.max_elapsed_time
            && self.start_time.unwrap().elapsed() >= max_elapsed
        {
            return None;
        }

        let delay = self.current_interval;

        // 计算下一次间隔
        let next_secs = self.current_interval.as_secs_f64() * self.multiplier;
        let next = Duration::from_secs_f64(next_secs.min(self.max_interval.as_secs_f64()));
        self.current_interval = next;

        // 添加 jitter
        if self.randomization_factor > 0.0 {
            let jitter = delay.as_secs_f64() * self.randomization_factor * rand::random::<f64>();
            Some(delay + Duration::from_secs_f64(jitter))
        } else {
            Some(delay)
        }
    }

    /// 重置退避状态
    /// state
    pub fn reset(&mut self) {
        self.current_interval = self.initial_interval;
        self.start_time = None;
    }
}

/// 对异步操作执行指数退避重试
/// to async index
///
/// 所有错误均视为可重试（transient），直到超过配置限制。
/// all as （transient），to 。
pub async fn retry_future<F, Fut, T, E>(
    mut operation: F,
    initial_interval: Duration,
    max_interval: Duration,
    max_elapsed_time: Option<Duration>,
) -> Result<T, E>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = Result<T, E>>,
{
    let start = Instant::now();
    let mut delay = initial_interval;

    loop {
        match operation().await {
            Ok(v) => return Ok(v),
            Err(e) => {
                // 检查累计时间限制
                if let Some(max) = max_elapsed_time
                    && start.elapsed() >= max
                {
                    return Err(e);
                }

                tokio::time::sleep(delay).await;

                // 指数增长并限制上限
                let next_secs = delay.as_secs_f64() * 2.0;
                delay = Duration::from_secs_f64(next_secs.min(max_interval.as_secs_f64()));
            }
        }
    }
}
