use anyhow::Result;
use backoff::{ExponentialBackoff, backoff::Backoff};
use dashmap::DashMap;
use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tokio::time::{sleep, timeout};
use tracing::{info, warn, error, debug};

/// 服务状态
#[derive(Debug, Clone, PartialEq)]
pub enum ServiceStatus {
    Healthy,
    Degraded,
    Unhealthy,
}

/// 服务实例
#[derive(Debug, Clone)]
pub struct ServiceInstance {
    pub id: String,
    pub url: String,
    pub status: ServiceStatus,
    pub last_health_check: Instant,
    pub response_time: Duration,
    pub error_count: u32,
}

/// 熔断器状态
#[derive(Debug, Clone, PartialEq)]
pub enum CircuitState {
    Closed,    // 正常状态
    Open,      // 熔断状态
    HalfOpen,  // 半开状态
}

/// 熔断器
#[derive(Debug)]
pub struct CircuitBreaker {
    state: Arc<RwLock<CircuitState>>,
    failure_threshold: u32,
    recovery_timeout: Duration,
    failure_count: Arc<RwLock<u32>>,
    last_failure_time: Arc<RwLock<Option<Instant>>>,
}

impl CircuitBreaker {
    pub fn new(failure_threshold: u32, recovery_timeout: Duration) -> Self {
        Self {
            state: Arc::new(RwLock::new(CircuitState::Closed)),
            failure_threshold,
            recovery_timeout,
            failure_count: Arc::new(RwLock::new(0)),
            last_failure_time: Arc::new(RwLock::new(None)),
        }
    }

    pub async fn call<F, T, E>(&self, operation: F) -> Result<T, E>
    where
        F: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Display + From<anyhow::Error>,
    {
        let state = self.state.read().await;
        
        match *state {
            CircuitState::Open => {
                // 检查是否可以进入半开状态
                if let Some(last_failure) = *self.last_failure_time.read().await {
                    if last_failure.elapsed() >= self.recovery_timeout {
                        drop(state);
                        self.transition_to_half_open().await;
                        // 重新检查状态并执行操作
                        let result = operation.await;
                        return match result {
                            Ok(value) => {
                                self.on_success().await;
                                Ok(value)
                            }
                            Err(e) => {
                                self.on_failure().await;
                                Err(e)
                            }
                        };
                    }
                }
                return Err(anyhow::anyhow!("Circuit breaker is open").into());
            }
            CircuitState::HalfOpen => {
                // 半开状态，尝试调用
                drop(state);
                match operation.await {
                    Ok(result) => {
                        self.on_success().await;
                        Ok(result)
                    }
                    Err(e) => {
                        self.on_failure().await;
                        Err(e)
                    }
                }
            }
            CircuitState::Closed => {
                // 正常状态
                drop(state);
                match operation.await {
                    Ok(result) => {
                        self.on_success().await;
                        Ok(result)
                    }
                    Err(e) => {
                        self.on_failure().await;
                        Err(e)
                    }
                }
            }
        }
    }

    async fn on_success(&self) {
        *self.failure_count.write().await = 0;
        *self.last_failure_time.write().await = None;
        
        let mut state = self.state.write().await;
        if *state == CircuitState::HalfOpen {
            *state = CircuitState::Closed;
            info!("Circuit breaker closed after successful call");
        }
    }

    async fn on_failure(&self) {
        let mut count = self.failure_count.write().await;
        *count += 1;
        *self.last_failure_time.write().await = Some(Instant::now());
        
        if *count >= self.failure_threshold {
            let mut state = self.state.write().await;
            *state = CircuitState::Open;
            warn!(failure_count = *count, "Circuit breaker opened due to failures");
        }
    }

    async fn transition_to_half_open(&self) {
        let mut state = self.state.write().await;
        *state = CircuitState::HalfOpen;
        info!("Circuit breaker transitioned to half-open state");
    }
}

/// 服务发现
#[derive(Debug)]
pub struct ServiceDiscovery {
    services: Arc<DashMap<String, Vec<ServiceInstance>>>,
    health_check_interval: Duration,
    circuit_breakers: Arc<DashMap<String, CircuitBreaker>>,
}

impl ServiceDiscovery {
    pub fn new(health_check_interval: Duration) -> Self {
        Self {
            services: Arc::new(DashMap::new()),
            health_check_interval,
            circuit_breakers: Arc::new(DashMap::new()),
        }
    }

    pub fn register_service(&self, service_name: &str, instances: Vec<ServiceInstance>) {
        self.services.insert(service_name.to_string(), instances);
        
        // 为每个服务创建熔断器
        for instance in self.services.get(service_name).unwrap().value() {
            self.circuit_breakers.insert(
                instance.id.clone(),
                CircuitBreaker::new(3, Duration::from_secs(30))
            );
        }
        
        info!(service_name, "Registered service with {} instances", 
              self.services.get(service_name).unwrap().value().len());
    }

    pub async fn get_healthy_instances(&self, service_name: &str) -> Vec<ServiceInstance> {
        if let Some(instances) = self.services.get(service_name) {
            instances.value()
                .iter()
                .filter(|instance| instance.status == ServiceStatus::Healthy)
                .cloned()
                .collect()
        } else {
            Vec::new()
        }
    }

    pub async fn call_service<T>(&self, service_name: &str, path: &str) -> Result<T>
    where
        T: for<'de> Deserialize<'de>,
    {
        let instances = self.get_healthy_instances(service_name).await;
        
        if instances.is_empty() {
            return Err(anyhow::anyhow!("No healthy instances available for service: {}", service_name));
        }

        // 简单的轮询负载均衡
        let instance = &instances[0]; // 简化实现
        
        if let Some(circuit_breaker) = self.circuit_breakers.get(&instance.id) {
            let url = format!("{}{}", instance.url, path);
            let client = Client::new();
            
            circuit_breaker.call(async {
                let response = client.get(&url).send().await?;
                let data: T = response.json().await?;
                Ok(data)
            }).await
        } else {
            Err(anyhow::anyhow!("Circuit breaker not found for instance: {}", instance.id))
        }
    }

    pub async fn start_health_checks(&self) {
        let services = self.services.clone();
        let _circuit_breakers = self.circuit_breakers.clone();
        let interval = self.health_check_interval;
        
        tokio::spawn(async move {
            let mut health_check_interval = tokio::time::interval(interval);
            let client = Client::new();
            
            loop {
                health_check_interval.tick().await;
                
                for service_entry in services.iter() {
                    let service_name = service_entry.key();
                    let mut instances = service_entry.value().clone();
                    
                    // 收集需要更新的实例ID
                    let instance_ids: Vec<String> = instances.iter().map(|i| i.id.clone()).collect();
                    
                    for instance_id in instance_ids {
                        let instance_url = instances.iter().find(|i| i.id == instance_id).unwrap().url.clone();
                        
                        // 执行健康检查
                        let health_check = async {
                            let start = Instant::now();
                            let response = timeout(
                                Duration::from_secs(5),
                                client.get(&format!("{}/health", instance_url)).send()
                            ).await??;
                            
                            let response_time = start.elapsed();
                            let is_healthy = response.status().is_success();
                            
                            Ok::<(bool, Duration), anyhow::Error>((is_healthy, response_time))
                        };
                        
                        match health_check.await {
                            Ok((is_healthy, response_time)) => {
                                debug!(
                                    service_name = %service_name,
                                    instance_id = %instance_id,
                                    response_time_ms = response_time.as_millis(),
                                    "Health check completed"
                                );
                                
                                // 更新实例状态
                                if let Some(instance) = instances.iter_mut().find(|i| i.id == instance_id) {
                                    instance.status = if is_healthy {
                                        ServiceStatus::Healthy
                                    } else {
                                        ServiceStatus::Unhealthy
                                    };
                                    instance.last_health_check = Instant::now();
                                    instance.response_time = response_time;
                                }
                            }
                            Err(e) => {
                                error!(
                                    service_name = %service_name,
                                    instance_id = %instance_id,
                                    error = %e,
                                    "Health check failed"
                                );
                                
                                if let Some(instance) = instances.iter_mut().find(|i| i.id == instance_id) {
                                    instance.status = ServiceStatus::Unhealthy;
                                    instance.error_count += 1;
                                }
                            }
                        }
                    }
                }
            }
        });
    }
}

/// 重试策略
pub struct RetryPolicy {
    max_retries: u32,
    backoff: ExponentialBackoff,
}

impl RetryPolicy {
    pub fn new(max_retries: u32) -> Self {
        Self {
            max_retries,
            backoff: ExponentialBackoff {
                initial_interval: Duration::from_millis(100),
                max_interval: Duration::from_secs(5),
                max_elapsed_time: Some(Duration::from_secs(30)),
                ..Default::default()
            },
        }
    }

    pub async fn execute<F, T, E>(&mut self, operation: F) -> Result<T>
    where
        F: Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>>,
        E: std::fmt::Display + Send + Sync + 'static,
    {
        let mut retries = 0;
        
        loop {
            match operation().await {
                Ok(result) => return Ok(result),
                Err(e) => {
                    if retries >= self.max_retries {
                        return Err(anyhow::anyhow!("Max retries exceeded: {}", e));
                    }
                    
                    retries += 1;
                    let delay = self.backoff.next_backoff().unwrap_or(Duration::from_secs(5));
                    
                    warn!(
                        retry = retries,
                        max_retries = self.max_retries,
                        delay_ms = delay.as_millis(),
                        error = %e,
                        "Retrying operation"
                    );
                    
                    sleep(delay).await;
                }
            }
        }
    }
}

#[derive(Serialize, Deserialize)]
struct UserData {
    id: u32,
    name: String,
    email: String,
}

#[tokio::main(flavor = "multi_thread")]
async fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();

    // 创建服务发现
    let service_discovery = Arc::new(ServiceDiscovery::new(Duration::from_secs(10)));
    
    // 注册用户服务实例
    service_discovery.register_service("user-service", vec![
        ServiceInstance {
            id: "user-1".to_string(),
            url: "http://localhost:8081".to_string(),
            status: ServiceStatus::Healthy,
            last_health_check: Instant::now(),
            response_time: Duration::ZERO,
            error_count: 0,
        },
        ServiceInstance {
            id: "user-2".to_string(),
            url: "http://localhost:8082".to_string(),
            status: ServiceStatus::Healthy,
            last_health_check: Instant::now(),
            response_time: Duration::ZERO,
            error_count: 0,
        },
    ]);

    // 启动健康检查
    service_discovery.start_health_checks().await;

    // 创建重试策略
    let mut retry_policy = RetryPolicy::new(3);

    // 模拟服务调用
    let service_discovery_clone = service_discovery.clone();
    
    let call_task = tokio::spawn(async move {
        for _i in 1..=10 {
            let result = retry_policy.execute(|| {
                let sd = service_discovery_clone.clone();
                Box::pin(async move {
                    sd.call_service::<UserData>("user-service", "/users/1").await
                })
            }).await;
            
            match result {
                Ok(user_data) => {
                    info!(user_id = user_data.id, "Successfully retrieved user data");
                }
                Err(e) => {
                    error!(error = %e, "Failed to retrieve user data");
                }
            }
            
            sleep(Duration::from_secs(2)).await;
        }
    });

    // 等待任务完成
    call_task.await?;
    
    info!("Microservice patterns demo completed");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_circuit_breaker() {
        let cb = CircuitBreaker::new(2, Duration::from_millis(100));
        
        // 第一次失败
        let result = cb.call(async { Err::<(), _>("error 1") }).await;
        assert!(result.is_err());
        
        // 第二次失败，应该打开熔断器
        let result = cb.call(async { Err::<(), _>("error 2") }).await;
        assert!(result.is_err());
        
        // 熔断器应该打开
        let result = cb.call(async { Ok::<(), _>(()) }).await;
        assert!(result.is_err());
        
        // 等待恢复时间
        sleep(Duration::from_millis(150)).await;
        
        // 应该进入半开状态
        let result = cb.call(async { Ok::<(), _>(()) }).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_retry_policy() {
        let policy = RetryPolicy::new(2);
        let mut attempts = 0;
        
        let result = policy.execute(|| {
            attempts += 1;
            Box::pin(async move {
                if attempts < 3 {
                    Err::<(), _>("temporary error")
                } else {
                    Ok(())
                }
            })
        }).await;
        
        assert!(result.is_ok());
        assert_eq!(attempts, 3);
    }
}
