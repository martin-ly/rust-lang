//! 编排监督：提供重启/退避/熔断与健康事件上报（与 Orchestrator 协作）
use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};
use super::orchestrator::{Orchestrator, WorkloadStatus};
use std::time::Duration;

#[derive(Debug, Clone)]
pub struct BackoffPolicy {
    pub initial: Duration,
    pub factor: f64,
    pub max: Duration,
    pub max_retries: u32,
}

impl Default for BackoffPolicy {
    fn default() -> Self {
        Self { initial: Duration::from_secs(1), factor: 2.0, max: Duration::from_secs(60), max_retries: 5 }
    }
}

pub struct OrchestratorSupervisor<O: Orchestrator> {
    orchestrator: O,
    backoff: BackoffPolicy,
}

impl<O: Orchestrator> OrchestratorSupervisor<O> {
    pub fn new(orchestrator: O, backoff: BackoffPolicy) -> Self { Self { orchestrator, backoff } }

    pub async fn ensure_running(&self, name: &str) -> Result<(), UnifiedError> {
        let mut delay = self.backoff.initial;
        let mut attempts = 0u32;
        loop {
            let st = self.orchestrator.status(name).await?;
            match st {
                WorkloadStatus::Running | WorkloadStatus::Succeeded => return Ok(()),
                WorkloadStatus::Pending => {},
                WorkloadStatus::Failed(_) => {
                    self.orchestrator.terminate(name).await.ok();
                    self.orchestrator.deploy(name).await?;
                }
            }
            if attempts >= self.backoff.max_retries { 
                return Err(UnifiedError::new(
                    "supervisor: exceeded max retries",
                    ErrorSeverity::High,
                    "orchestrator_supervisor",
                    ErrorContext::new("orchestrator_supervisor","ensure_running", file!(), line!(), ErrorSeverity::High, "orchestrator_supervisor")
                ));
            }
            tokio::time::sleep(delay).await;
            attempts += 1;
            let next = (delay.as_secs_f64() * self.backoff.factor).min(self.backoff.max.as_secs_f64());
            delay = Duration::from_secs_f64(next);
        }
    }
}


