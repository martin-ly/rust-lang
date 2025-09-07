use crate::errors::DistributedError;

pub trait RpcClient {
    fn call(&self, method: &str, payload: &[u8]) -> Result<Vec<u8>, DistributedError>;
}

pub trait RpcServer {
    fn register(&mut self, method: &str, handler: Box<dyn Fn(&[u8]) -> Vec<u8> + Send + Sync>);
}

use std::collections::HashMap;
use std::sync::{Arc, RwLock};

#[derive(Default, Clone)]
pub struct InMemoryRpcServer {
    handlers: Arc<RwLock<HashMap<String, Arc<dyn Fn(&[u8]) -> Vec<u8> + Send + Sync>>>>,
}

impl InMemoryRpcServer {
    pub fn new() -> Self { Self::default() }
}

impl RpcServer for InMemoryRpcServer {
    fn register(&mut self, method: &str, handler: Box<dyn Fn(&[u8]) -> Vec<u8> + Send + Sync>) {
        self.handlers
            .write()
            .expect("lock")
            .insert(method.to_string(), handler.into());
    }
}

#[derive(Clone)]
pub struct InMemoryRpcClient {
    server: InMemoryRpcServer,
}

impl InMemoryRpcClient {
    pub fn new(server: InMemoryRpcServer) -> Self { Self { server } }
}

impl RpcClient for InMemoryRpcClient {
    fn call(&self, method: &str, payload: &[u8]) -> Result<Vec<u8>, DistributedError> {
        let handlers = self.server.handlers.read().map_err(|_| DistributedError::Network("lock poisoned".into()))?;
        let f = handlers.get(method).ok_or_else(|| DistributedError::Network(format!("method not found: {}", method)))?;
        Ok(f(payload))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct RetryPolicy {
    pub max_retries: usize,
    pub retry_on_empty: bool,
    pub backoff_base_ms: Option<u64>,
}

pub struct RetryClient<C: RpcClient> {
    pub inner: C,
    pub policy: RetryPolicy,
}

impl<C: RpcClient> RpcClient for RetryClient<C> {
    fn call(&self, method: &str, payload: &[u8]) -> Result<Vec<u8>, DistributedError> {
        let mut last_err: Option<DistributedError> = None;
        for attempt in 0..=self.policy.max_retries {
            match self.inner.call(method, payload) {
                Ok(v) => {
                    if self.policy.retry_on_empty && v.is_empty() {
                        if let Some(base) = self.policy.backoff_base_ms {
                            let delay = base.saturating_mul(1u64 << attempt.min(16));
                            std::thread::sleep(std::time::Duration::from_millis(delay));
                        }
                        continue;
                    }
                    return Ok(v);
                }
                Err(e) => { last_err = Some(e); }
            }
            if let Some(base) = self.policy.backoff_base_ms {
                let delay = base.saturating_mul(1u64 << attempt.min(16));
                std::thread::sleep(std::time::Duration::from_millis(delay));
            }
        }
        Err(last_err.unwrap_or_else(|| DistributedError::Network("retry failed".into())))
    }
}

