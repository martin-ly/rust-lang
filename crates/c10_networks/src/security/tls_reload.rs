use crate::error::{NetworkError, NetworkResult};
use rustls::ServerConfig;
use rustls::crypto::ring;
use rustls::pki_types::{
    CertificateDer, PrivateKeyDer, PrivatePkcs1KeyDer, PrivatePkcs8KeyDer, PrivateSec1KeyDer,
};
use rustls::version::TLS13;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 线程安全的 TLS 配置热重载容器
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
        let provider = ring::default_provider();
        let new = ServerConfig::builder_with_provider(provider.into())
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
    let mut certs = vec![];
    let mut rest = pem;
    while let Some((block, r)) = rustls_pemfile::read_one_from_slice(rest)
        .map_err(|e| NetworkError::Other(format!("{e:?}")))?
    {
        rest = r;
        if let rustls_pemfile::Item::X509Certificate(der) = block {
            certs.push(CertificateDer::from(der));
        }
    }
    if certs.is_empty() {
        return Err(NetworkError::Other("no certs in pem".into()));
    }
    Ok(certs)
}

fn pemfile_to_key(pem: &[u8]) -> NetworkResult<PrivateKeyDer<'static>> {
    let mut rest = pem;
    while let Some((block, r)) = rustls_pemfile::read_one_from_slice(rest)
        .map_err(|e| NetworkError::Other(format!("{e:?}")))?
    {
        rest = r;
        match block {
            // 转换为 pki_types
            rustls_pemfile::Item::Pkcs8Key(der) => {
                return Ok(PrivateKeyDer::from(PrivatePkcs8KeyDer::from(der)));
            }
            rustls_pemfile::Item::Pkcs1Key(der) => {
                return Ok(PrivateKeyDer::from(PrivatePkcs1KeyDer::from(der)));
            }
            rustls_pemfile::Item::Sec1Key(der) => {
                return Ok(PrivateKeyDer::from(PrivateSec1KeyDer::from(der)));
            }
            _ => {}
        }
    }
    Err(NetworkError::Other("no private key in pem".into()))
}
