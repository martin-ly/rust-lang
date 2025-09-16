// 使用 hyper 直接提供最小 HTTP 服务，避免 hyper/axum 版本耦合导致的适配复杂度
use bytes::Bytes;
use c10_networks::{AcmeManager, Http01MemoryStore, TlsReloader};
use http_body_util::Full;
use hyper::{Request, Response, StatusCode, body::Incoming as HyperIncoming};
use rustls::ServerConfig;
use rustls::crypto::ring;
use rustls::pki_types::{
    CertificateDer, PrivateKeyDer, PrivatePkcs1KeyDer, PrivatePkcs8KeyDer, PrivateSec1KeyDer,
};
use rustls::version::TLS13;
use std::net::SocketAddr;
use std::path::PathBuf;
//use std::sync::Arc;
//use tokio::sync::RwLock;
use hyper_util::rt::TokioIo;
use hyper_util::server::conn::auto::Builder as AutoBuilder;
use std::sync::Arc;
use tokio_rustls::TlsAcceptor;
//use tokio::sync::RwLock;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 占位：使用自签名或已有证书，构造初始 TLS 配置
    // 使用 rcgen 生成自签名证书，避免依赖外部测试文件
    let (cert_pem, key_pem) = self_signed_cert()?;
    let certs = pem_to_certs(cert_pem)?;
    let key = pem_to_key(key_pem)?;
    let provider = ring::default_provider();
    let config = ServerConfig::builder_with_provider(provider.into())
        .with_protocol_versions(&[&TLS13])
        .map_err(|e| anyhow::anyhow!("tls proto: {e}"))?
        .with_no_client_auth()
        .with_single_cert(certs, key)
        .map_err(|e| anyhow::anyhow!("tls build: {e}"))?;
    let reloader = TlsReloader::new(config);
    let tls_config = reloader.handle();

    let store = Http01MemoryStore::new();
    // 占位：真实 ACME 流程会写入 store.set(token, keyAuth)
    store
        .set("example-token".to_string(), "example-key-auth".to_string())
        .await;

    let addr: SocketAddr = "0.0.0.0:443".parse()?;
    println!("listening on https://{addr}");

    let listener = tokio::net::TcpListener::bind(addr).await?;

    // 启动占位 AcmeManager：自动生成/读取 ./acme 证书并配合文件监控触发热重载
    let mut mgr = AcmeManager::new(
        std::path::PathBuf::from("./acme"),
        "https://acme-staging-v02.api.letsencrypt.org/directory",
        vec!["example.org".to_string(), "www.example.org".to_string()],
    );
    mgr.contact_email = Some("admin@example.org".to_string());
    mgr.http01_store = Some(store.clone());
    let _ = mgr.spawn_renew_task().await; // 占位后台任务（首次会尝试生成/读取证书）

    // 文件变更监控：当 cert.pem 或 key.pem 变动时，热重载
    let reload_task = reloader.clone();
    tokio::spawn(async move {
        let cert_path = PathBuf::from("./acme/cert.pem");
        let key_path = PathBuf::from("./acme/key.pem");
        let mut last_sig = (0u64, 0u64);
        loop {
            let sig = (
                file_sig(&cert_path).unwrap_or(0),
                file_sig(&key_path).unwrap_or(0),
            );
            if sig != (0, 0) && sig != last_sig {
                if let (Ok(cert), Ok(key)) = (
                    tokio::fs::read(&cert_path).await,
                    tokio::fs::read(&key_path).await,
                ) {
                    let _ = reload_task.reload(&cert, &key).await;
                }
                last_sig = sig;
            }
            tokio::time::sleep(std::time::Duration::from_secs(3)).await;
        }
    });

    // 启动基于 hyper 1 + tokio-rustls 的 TLS 服务器，按连接获取最新配置
    loop {
        let (tcp, peer) = listener.accept().await?;
        let tls_config = tls_config.clone();
        let store = store.clone();
        tokio::spawn(async move {
            let cfg = { tls_config.read().await.clone() };
            let acceptor = TlsAcceptor::from(Arc::new(cfg));
            match acceptor.accept(tcp).await {
                Ok(tls_stream) => {
                    let io = TokioIo::new(tls_stream);
                    let service = hyper::service::service_fn(move |req: Request<HyperIncoming>| {
                        let store = store.clone();
                        async move {
                            let path = req.uri().path().to_string();
                            if let Some(token) = path.strip_prefix("/.well-known/acme-challenge/") {
                                let body = store.get(token).await.unwrap_or_default();
                                let resp = Response::builder()
                                    .status(StatusCode::OK)
                                    .body(Full::new(Bytes::from(body)))
                                    .unwrap();
                                Ok::<_, hyper::Error>(resp)
                            } else {
                                let resp = Response::builder()
                                    .status(StatusCode::NOT_FOUND)
                                    .body(Full::new(Bytes::from_static(b"not found")))
                                    .unwrap();
                                Ok::<_, hyper::Error>(resp)
                            }
                        }
                    });
                    if let Err(e) = AutoBuilder::new(hyper_util::rt::TokioExecutor::new())
                        .serve_connection(io, service)
                        .await
                    {
                        eprintln!("serve_connection error from {peer:?}: {e}");
                    }
                }
                Err(e) => eprintln!("tls accept error from {peer:?}: {e}"),
            }
        });
    }
}

fn pem_to_certs(pem: &[u8]) -> anyhow::Result<Vec<CertificateDer<'static>>> {
    let mut certs = vec![];
    let mut rest = pem;
    while let Some((item, r)) =
        rustls_pemfile::read_one_from_slice(rest).map_err(|e| anyhow::anyhow!("{e:?}"))?
    {
        rest = r;
        if let rustls_pemfile::Item::X509Certificate(der) = item {
            certs.push(CertificateDer::from(der));
        }
    }
    anyhow::ensure!(!certs.is_empty(), "no certs in pem");
    Ok(certs)
}

fn pem_to_key(pem: &[u8]) -> anyhow::Result<PrivateKeyDer<'static>> {
    let mut rest = pem;
    while let Some((item, r)) =
        rustls_pemfile::read_one_from_slice(rest).map_err(|e| anyhow::anyhow!("{e:?}"))?
    {
        rest = r;
        match item {
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
    anyhow::bail!("no key in pem")
}

fn self_signed_cert() -> anyhow::Result<(&'static [u8], &'static [u8])> {
    let rcgen::CertifiedKey { cert, signing_key } =
        rcgen::generate_simple_self_signed(["localhost".to_string()])?;
    let cert_pem = cert.pem().into_bytes();
    let key_pem = signing_key.serialize_pem().into_bytes();
    // 将 Vec 泄漏为 'static 以简化示例生命周期
    let cert_pem_static: &'static [u8] = Box::leak(cert_pem.into_boxed_slice());
    let key_pem_static: &'static [u8] = Box::leak(key_pem.into_boxed_slice());
    Ok((cert_pem_static, key_pem_static))
}

fn file_sig(path: &PathBuf) -> Option<u64> {
    let md = std::fs::metadata(path).ok()?;
    let len = md.len();
    let mt = md.modified().ok()?.elapsed().ok()?.as_secs();
    Some(len ^ mt)
}
