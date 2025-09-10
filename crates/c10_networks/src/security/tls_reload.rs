use crate::error::{NetworkError, NetworkResult};
use rustls::{Certificate, PrivateKey, ServerConfig};
use std::sync::Arc;
use tokio::sync::RwLock;

/// 线程安全的 TLS 配置热重载容器
#[derive(Clone)]
pub struct TlsReloader(Arc<RwLock<ServerConfig>>);

impl TlsReloader {
    pub fn new(config: ServerConfig) -> Self {
        Self(Arc::new(RwLock::new(config)))
    }

    pub fn handle(&self) -> Arc<RwLock<ServerConfig>> { self.0.clone() }

    pub async fn reload(&self, cert_chain_pem: &[u8], key_pem: &[u8]) -> NetworkResult<()> {
        let certs = pemfile_to_certs(cert_chain_pem)?;
        let key = pemfile_to_key(key_pem)?;
        let new = ServerConfig::builder()
            .with_safe_defaults()
            .with_no_client_auth()
            .with_single_cert(certs, key)
            .map_err(|e| NetworkError::Other(format!("tls build: {e}")))?;
        *self.0.write().await = new;
        Ok(())
    }
}

fn pemfile_to_certs(pem: &[u8]) -> NetworkResult<Vec<Certificate>> {
    let mut certs = vec![];
    let mut rest = pem;
    while let Some((block, r)) = rustls_pemfile::read_one_from_slice(rest).map_err(|e| NetworkError::Other(e.to_string()))? {
        rest = r;
        if let rustls_pemfile::Item::X509Certificate(der) = block { certs.push(Certificate(der)); }
    }
    if certs.is_empty() { return Err(NetworkError::Other("no certs in pem".into())); }
    Ok(certs)
}

fn pemfile_to_key(pem: &[u8]) -> NetworkResult<PrivateKey> {
    let mut rest = pem;
    while let Some((block, r)) = rustls_pemfile::read_one_from_slice(rest).map_err(|e| NetworkError::Other(e.to_string()))? {
        rest = r;
        match block {
            rustls_pemfile::Item::Pkcs8Key(der) => return Ok(PrivateKey(der)),
            rustls_pemfile::Item::Pkcs1Key(der) => return Ok(PrivateKey(der)),
            rustls_pemfile::Item::Sec1Key(der) => return Ok(PrivateKey(der)),
            _ => {}
        }
    }
    Err(NetworkError::Other("no private key in pem".into()))
}


