use crate::error::{NetworkError, NetworkResult};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;

/// ACME 管理器：负责账户、订单、挑战处理与证书续期调度
pub struct AcmeManager {
    /// 账户与证书的持久化目录
    pub storage_dir: PathBuf,
    /// ACME 目录 URL（生产/测试）
    pub directory_url: String,
    /// 域名列表
    pub domains: Vec<String>,
}

impl AcmeManager {
    pub fn new(storage_dir: PathBuf, directory_url: impl Into<String>, domains: Vec<String>) -> Self {
        Self { storage_dir, directory_url: directory_url.into(), domains }
    }

    /// 证书链 PEM 文件路径（默认 storage_dir/cert.pem）
    pub fn cert_pem_path(&self) -> PathBuf { self.storage_dir.join("cert.pem") }

    /// 私钥 PEM 文件路径（默认 storage_dir/key.pem）
    pub fn key_pem_path(&self) -> PathBuf { self.storage_dir.join("key.pem") }

    /// 启动后台续期任务（占位实现）
    pub async fn spawn_renew_task(&self) -> NetworkResult<()> {
        let _interval = Duration::from_secs(60 * 60 * 12);
        let mgr = self.clone_for_task();
        tokio::spawn(async move {
            // 首次生成
            let _ = mgr.obtain_or_renew_now().await;
            loop {
                tokio::time::sleep(_interval).await;
                let _ = mgr.obtain_or_renew_now().await;
            }
        });
        Ok(())
    }

    /// 触发一次立即申请/续期（占位实现）
    pub async fn obtain_or_renew_now(&self) -> NetworkResult<(Vec<u8>, Vec<u8>)> {
        // TODO: 使用 instant-acme 替换为真实申请/续期；当前占位：若磁盘已有证书，则读取返回
        let cert_path = self.cert_pem_path();
        let key_path = self.key_pem_path();
        if cert_path.exists() && key_path.exists() {
            let cert_pem = std::fs::read(cert_path).map_err(|e| NetworkError::Other(e.to_string()))?;
            let key_pem = std::fs::read(key_path).map_err(|e| NetworkError::Other(e.to_string()))?;
            return Ok((cert_pem, key_pem));
        }
        Err(NetworkError::Other("ACME obtain/renew not implemented".into()))
    }

    fn clone_for_task(&self) -> Self {
        Self { storage_dir: self.storage_dir.clone(), directory_url: self.directory_url.clone(), domains: self.domains.clone() }
    }

}

/// 简易的 HTTP-01 挑战存储（token -> keyAuthorization）
#[derive(Clone, Default)]
pub struct Http01MemoryStore {
    inner: Arc<RwLock<HashMap<String, String>>>,
}

impl Http01MemoryStore {
    pub fn new() -> Self { Self { inner: Arc::new(RwLock::new(HashMap::new())) } }

    pub async fn set(&self, token: String, key_authorization: String) {
        self.inner.write().await.insert(token, key_authorization);
    }

    pub async fn get(&self, token: &str) -> Option<String> {
        self.inner.read().await.get(token).cloned()
    }

    pub async fn remove(&self, token: &str) {
        self.inner.write().await.remove(token);
    }
}


