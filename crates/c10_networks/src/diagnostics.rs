use crate::error::NetworkError;
use std::net::{TcpStream, ToSocketAddrs};
use std::time::Duration;

#[derive(Debug, Clone)]
pub struct NetDiagnostics;

#[derive(Debug, Clone)]
pub struct ConnectivityReport {
    pub dns_ok: bool,
    pub tcp_connect_ok: bool,
    pub latency_ms: Option<u128>,
}

impl NetDiagnostics {
    pub fn new() -> Self { Self }

    /// DNS 解析自检
    pub fn check_dns(&self, host: &str) -> bool {
        (host, 0).to_socket_addrs().is_ok()
    }

    /// TCP 连通性检测（带超时）
    pub fn check_tcp_connect(&self, addr: &str, timeout_ms: u64) -> ConnectivityReport {
        let start = std::time::Instant::now();
        let dns_ok = addr.to_socket_addrs().is_ok();
        let tcp_connect_ok = TcpStream::connect_timeout(
            &addr.to_socket_addrs().ok().and_then(|mut it| it.next()).unwrap_or_else(|| "127.0.0.1:9".parse().unwrap()),
            Duration::from_millis(timeout_ms),
        ).is_ok();
        let latency_ms = if tcp_connect_ok { Some(start.elapsed().as_millis()) } else { None };
        ConnectivityReport { dns_ok, tcp_connect_ok, latency_ms }
    }

    /// 统一错误建议（示例）
    pub fn suggest(&self, err: &NetworkError) -> &'static str {
        match err {
            NetworkError::Timeout(_) => "检查目标服务可达性与超时时间，考虑重试与退避策略",
            NetworkError::Connection(_) => "检查 DNS、端口、证书与网络代理设置",
            NetworkError::Protocol(_) => "检查报文格式、版本与兼容性；建议抓包定位",
            _ => "启用 tracing 日志并复现收集上下文"
        }
    }

    /// 异步 TCP 连通性检测（Tokio）
    pub async fn tcp_connect_async(&self, addr: &str, timeout_ms: u64) -> ConnectivityReport {
        let start = std::time::Instant::now();
        let dns_ok = addr.to_socket_addrs().is_ok();
        let fut = tokio::net::TcpStream::connect(addr);
        let tcp_connect_ok = match tokio::time::timeout(Duration::from_millis(timeout_ms), fut).await {
            Ok(Ok(_stream)) => true,
            _ => false,
        };
        let latency_ms = if tcp_connect_ok { Some(start.elapsed().as_millis()) } else { None };
        ConnectivityReport { dns_ok, tcp_connect_ok, latency_ms }
    }

    /// 扫描指定端口集合，返回开放端口（异步）
    pub async fn scan_tcp_ports(&self, host: &str, ports: &[u16], timeout_ms: u64) -> Vec<u16> {
        let mut open = Vec::new();
        for &p in ports {
            let addr = format!("{}:{}", host, p);
            let fut = tokio::net::TcpStream::connect(&addr);
            let ok = match tokio::time::timeout(Duration::from_millis(timeout_ms), fut).await {
                Ok(Ok(_)) => true,
                _ => false,
            };
            if ok { open.push(p); }
        }
        open
    }

    /// 代理环境变量探测（HTTP(S)_PROXY）
    pub fn detect_proxy_env(&self) -> std::collections::HashMap<String, String> {
        let mut m = std::collections::HashMap::new();
        for k in ["HTTP_PROXY", "http_proxy", "HTTPS_PROXY", "https_proxy", "ALL_PROXY", "all_proxy"] {
            if let Ok(v) = std::env::var(k) { if !v.is_empty() { m.insert(k.to_string(), v); } }
        }
        m
    }

    /// 使用 tracing 输出错误与建议
    pub fn trace_with_suggestion(&self, err: &NetworkError) {
        let tip = self.suggest(err);
        tracing::error!(error = %err, suggestion = %tip, "network error");
    }

    /// 初始化 tracing（幂等）
    pub fn init_tracing_default(&self) {
        static ONCE: std::sync::Once = std::sync::Once::new();
        ONCE.call_once(|| {
            let _ = tracing_subscriber::fmt::try_init();
        });
    }

    /// 简单的带指数退避的重试器（异步）
    pub async fn retry_with_backoff<T, F, Fut>(&self, attempts: usize, base_delay_ms: u64, mut op: F) -> Result<T, NetworkError>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = Result<T, NetworkError>>,
    {
        let mut delay = base_delay_ms.max(1);
        let mut last_err: Option<NetworkError> = None;
        for i in 0..attempts {
            match op().await {
                Ok(v) => return Ok(v),
                Err(e) => {
                    last_err = Some(e);
                    if i + 1 < attempts {
                        tokio::time::sleep(Duration::from_millis(delay)).await;
                        delay = (delay.saturating_mul(2)).min(30_000);
                    }
                }
            }
        }
        Err(last_err.unwrap_or_else(|| NetworkError::Other("retry failed".into())))
    }
}


