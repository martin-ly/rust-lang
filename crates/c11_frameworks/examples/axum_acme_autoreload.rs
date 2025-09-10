use axum::{routing::get, extract::Path, Router};
use c10_networks::{TlsReloader, Http01MemoryStore};
use std::path::PathBuf;
use rustls::{Certificate, PrivateKey, ServerConfig};
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::sync::RwLock;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 占位：使用自签名或已有证书，构造初始 TLS 配置
    let cert_pem = include_bytes!("../../c10_networks/tests/data/server.crt");
    let key_pem = include_bytes!("../../c10_networks/tests/data/server.key");
    let certs = pem_to_certs(cert_pem)?;
    let key = pem_to_key(key_pem)?;
    let config = ServerConfig::builder()
        .with_safe_defaults()
        .with_no_client_auth()
        .with_single_cert(certs, key)?;
    let reloader = TlsReloader::new(config);
    let tls_config: Arc<RwLock<ServerConfig>> = reloader.handle();

    let store = Http01MemoryStore::new();
    // 占位：真实 ACME 流程会写入 store.set(token, keyAuth)
    store.set("example-token".to_string(), "example-key-auth".to_string()).await;

    let app = Router::new().route("/.well-known/acme-challenge/:token", get({
        let store = store.clone();
        move |Path(token): Path<String>| {
            let store = store.clone();
            async move { store.get(&token).await.unwrap_or_default() }
        }
    }));

    let addr: SocketAddr = "0.0.0.0:443".parse()?;
    println!("listening on https://{addr}");

    let listener = tokio::net::TcpListener::bind(addr).await?;
    let incoming = tokio_stream::wrappers::TcpListenerStream::new(listener);
    let acceptor = tokio_rustls::TlsAcceptor::from(tls_config.clone());
    let svc = app.into_make_service();

    // 文件变更监控：当 cert.pem 或 key.pem 变动时，热重载
    let reload_task = reloader.clone();
    tokio::spawn(async move {
        let cert_path = PathBuf::from("./acme/cert.pem");
        let key_path = PathBuf::from("./acme/key.pem");
        let mut last_sig = (0u64, 0u64);
        loop {
            let sig = (file_sig(&cert_path).unwrap_or(0), file_sig(&key_path).unwrap_or(0));
            if sig != (0, 0) && sig != last_sig {
                if let (Ok(cert), Ok(key)) = (tokio::fs::read(&cert_path).await, tokio::fs::read(&key_path).await) {
                    let _ = reload_task.reload(&cert, &key).await;
                }
                last_sig = sig;
            }
            tokio::time::sleep(std::time::Duration::from_secs(3)).await;
        }
    });

    hyper::Server::builder(hyper::server::accept::from_stream(async_stream::stream! {
        use tokio::io::{AsyncRead, AsyncWrite};
        use futures_util::TryStreamExt;
        let mut inc = incoming;
        while let Some(conn) = inc.try_next().await.unwrap_or(None) {
            let acceptor = acceptor.clone();
            let tls = async move {
                match acceptor.accept(conn).await {
                    Ok(stream) => Ok::<_, std::io::Error>(stream),
                    Err(_e) => Err(std::io::Error::new(std::io::ErrorKind::Other, "tls accept")),
                }
            };
            yield tls.await;
        }
    }))
    .serve(svc)
    .await?;

    Ok(())
}

fn pem_to_certs(pem: &[u8]) -> anyhow::Result<Vec<Certificate>> {
    let mut certs = vec![];
    let mut rest = pem;
    while let Some((item, r)) = rustls_pemfile::read_one_from_slice(rest)? {
        rest = r;
        if let rustls_pemfile::Item::X509Certificate(der) = item { certs.push(Certificate(der)); }
    }
    anyhow::ensure!(!certs.is_empty(), "no certs in pem");
    Ok(certs)
}

fn pem_to_key(pem: &[u8]) -> anyhow::Result<PrivateKey> {
    let mut rest = pem;
    while let Some((item, r)) = rustls_pemfile::read_one_from_slice(rest)? {
        rest = r;
        match item {
            rustls_pemfile::Item::Pkcs8Key(der) => return Ok(PrivateKey(der)),
            rustls_pemfile::Item::Pkcs1Key(der) => return Ok(PrivateKey(der)),
            rustls_pemfile::Item::Sec1Key(der) => return Ok(PrivateKey(der)),
            _ => {}
        }
    }
    anyhow::bail!("no key in pem")
}

fn file_sig(path: &PathBuf) -> Option<u64> {
    let md = std::fs::metadata(path).ok()?;
    let len = md.len();
    let mt = md.modified().ok()?.elapsed().ok()?.as_secs();
    Some(len ^ mt)
}


