use crate::error::{NetworkError, NetworkResult};
use rustls::ServerConfig;
use rustls::crypto::CryptoProvider;
use rustls::pki_types::{CertificateDer, PrivateKeyDer};
use rustls::version::TLS13;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 线程安全的 TLS 配置热重载容器
/// thread-safe TLS
#[derive(Clone)]
pub struct TlsReloader(Arc<RwLock<ServerConfig>>);

impl TlsReloader {
    pub fn new(config: ServerConfig) -> Self {
        Self(Arc::new(RwLock::new(config)))
    }

    pub fn handle(&self) -> Arc<RwLock<ServerConfig>> {
        self.0.clone()
    }

    pub async fn reload(&self, cert_chain_pem: &[u8], key_pem: &[u8]) -> NetworkResult<()> {
        let certs: Vec<CertificateDer<'static>> = pemfile_to_certs(cert_chain_pem)?;
        let key: PrivateKeyDer<'static> = pemfile_to_key(key_pem)?;
        let provider = CryptoProvider::get_default()
            .cloned()
            .unwrap_or_else(|| Arc::new(rustls::crypto::aws_lc_rs::default_provider()));
        let new = ServerConfig::builder_with_provider(provider)
            .with_protocol_versions(&[&TLS13])
            .map_err(|e| NetworkError::Other(format!("tls proto: {e}")))?
            .with_no_client_auth()
            .with_single_cert(certs, key)
            .map_err(|e| NetworkError::Other(format!("tls build: {e}")))?;
        *self.0.write().await = new;
        Ok(())
    }
}

fn pemfile_to_certs(pem: &[u8]) -> NetworkResult<Vec<CertificateDer<'static>>> {
    use rustls::pki_types::pem::PemObject;
    let certs: Vec<_> = CertificateDer::pem_slice_iter(pem)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| NetworkError::Other(format!("{e:?}")))?;
    if certs.is_empty() {
        return Err(NetworkError::Other("no certs in pem".into()));
    }
    Ok(certs)
}

fn pemfile_to_key(pem: &[u8]) -> NetworkResult<PrivateKeyDer<'static>> {
    use rustls::pki_types::pem::PemObject;
    PrivateKeyDer::from_pem_slice(pem)
        .map_err(|e| NetworkError::Other(format!("{e:?}")))
}
