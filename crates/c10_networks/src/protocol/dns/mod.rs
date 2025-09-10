use crate::error::{NetworkError, NetworkResult};
use hickory_resolver::config::{ResolverConfig, ResolverOpts};
use hickory_resolver::error::ResolveErrorKind;
use hickory_resolver::name_server::{GenericConnector, TokioRuntimeProvider};
use hickory_resolver::proto::rr::rdata::SRV;
use hickory_resolver::TokioAsyncResolver;
use std::net::{IpAddr, SocketAddr};
use std::time::Duration;

/// DNS 解析器封装（基于 Hickory-DNS）
#[derive(Clone)]
pub struct DnsResolver {
    inner: TokioAsyncResolver,
}

impl std::fmt::Debug for DnsResolver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DnsResolver").finish()
    }
}

impl DnsResolver {
    /// 使用系统 DNS 配置创建解析器（/etc/resolv.conf、Registry 等）
    pub async fn from_system() -> NetworkResult<Self> {
        let resolver = TokioAsyncResolver::tokio_from_system_conf()
            .map_err(|e| NetworkError::Other(format!("dns system config: {e}")))?;
        Ok(Self { inner: resolver })
    }

    /// 使用给定配置与选项创建解析器（支持自定义 DoT/DoH）
    pub async fn from_config(config: ResolverConfig, mut opts: ResolverOpts) -> NetworkResult<Self> {
        // 合理的超时与并发（可通过环境变量覆盖）
        if let Some(ms) = std::env::var("C10_DNS_TIMEOUT_MS").ok().and_then(|s| s.parse::<u64>().ok()) {
            opts.timeout = Duration::from_millis(ms.max(1));
        } else {
            opts.timeout = Duration::from_secs(5);
        }
        if let Some(attempts) = std::env::var("C10_DNS_ATTEMPTS").ok().and_then(|s| s.parse::<usize>().ok()) {
            opts.attempts = attempts.max(1);
        } else {
            opts.attempts = 2;
        }
        let connector = GenericConnector::new(TokioRuntimeProvider::default());
        let resolver = TokioAsyncResolver::new(config, opts, connector);
        Ok(Self { inner: resolver })
    }

    /// 查询 A/AAAA 记录，返回 IP 列表（自动合并）
    pub async fn lookup_ips(&self, host: &str) -> NetworkResult<Vec<IpAddr>> {
        let lookup = self
            .inner
            .lookup_ip(host)
            .await
            .map_err(|e| Self::map_resolve_err(host, "A/AAAA lookup failed", Some(e)))?;
        Ok(lookup.iter().collect())
    }

    /// 查询 TXT 记录
    pub async fn lookup_txt(&self, name: &str) -> NetworkResult<Vec<String>> {
        let txt = self.inner.txt_lookup(name).await
            .map_err(|e| Self::map_resolve_err(name, "TXT lookup failed", Some(e)))?;
        Ok(txt
            .iter()
            .flat_map(|r| r.txt_data().iter())
            .map(|bytes| String::from_utf8_lossy(bytes).to_string())
            .collect())
    }

    /// 查询 MX 记录
    pub async fn lookup_mx(&self, name: &str) -> NetworkResult<Vec<(u16, String)>> {
        let mx = self.inner.mx_lookup(name).await
            .map_err(|e| Self::map_resolve_err(name, "MX lookup failed", Some(e)))?;
        Ok(mx.iter().map(|r| (r.preference(), r.exchange().to_utf8())).collect())
    }

    /// 查询 SRV 记录
    pub async fn lookup_srv(&self, name: &str) -> NetworkResult<Vec<(SRV, String)>> {
        let srv = self.inner.srv_lookup(name).await
            .map_err(|e| Self::map_resolve_err(name, "SRV lookup failed", Some(e)))?;
        Ok(srv.iter().map(|r| (r.clone(), r.target().to_utf8())).collect())
    }

    /// 逆向解析（PTR）
    pub async fn reverse_lookup(&self, addr: IpAddr) -> NetworkResult<Vec<String>> {
        let ptr = self.inner.reverse_lookup(addr).await
            .map_err(|e| NetworkError::Other(format!("dns reverse {addr}: {e}")))?;
        Ok(ptr.iter().map(|r| r.to_utf8()).collect())
    }

    /// 将域名解析为可连接的 SocketAddr（带端口）
    pub async fn resolve_socket_addrs(&self, host: &str, port: u16) -> NetworkResult<Vec<SocketAddr>> {
        let ips = self.lookup_ips(host).await?;
        Ok(ips.into_iter().map(|ip| SocketAddr::new(ip, port)).collect())
    }

    fn map_resolve_err(target: &str, ctx: &str, err: Option<hickory_resolver::error::ResolveError>) -> NetworkError {
        if let Some(e) = err {
            match e.kind() {
                ResolveErrorKind::NoRecordsFound { .. } => NetworkError::Protocol(format!("DNS no records for {target}: {ctx}")),
                ResolveErrorKind::Timeout => NetworkError::Timeout(Duration::from_secs(5)),
                other => NetworkError::Other(format!("DNS resolve {target} failed: {ctx}: {other}")),
            }
        } else {
            NetworkError::Other(format!("DNS resolve {target} failed: {ctx}"))
        }
    }
}

/// 常用预设：Cloudflare DoH 与 DoT
pub mod presets {
    use super::*;

    /// Cloudflare DoH: https://cloudflare-dns.com/dns-query
    pub fn cloudflare_doh() -> (ResolverConfig, ResolverOpts) {
        (ResolverConfig::cloudflare_https(), ResolverOpts::default())
    }

    /// Cloudflare DoT: 1.1.1.1:853 with SNI
    pub fn cloudflare_dot() -> (ResolverConfig, ResolverOpts) {
        (ResolverConfig::cloudflare_tls(), ResolverOpts::default())
    }

    /// Google DoH: https://dns.google/dns-query
    pub fn google_doh() -> (ResolverConfig, ResolverOpts) {
        (ResolverConfig::google_https(), ResolverOpts::default())
    }

    /// Google DoT: 8.8.8.8:853 with SNI dns.google
    pub fn google_dot() -> (ResolverConfig, ResolverOpts) {
        (ResolverConfig::google_tls(), ResolverOpts::default())
    }

    /// Quad9 DoH: https://dns.quad9.net/dns-query
    pub fn quad9_doh() -> (ResolverConfig, ResolverOpts) {
        (ResolverConfig::quad9_https(), ResolverOpts::default())
    }

    /// Quad9 DoT: 9.9.9.9:853 with SNI dns.quad9.net
    pub fn quad9_dot() -> (ResolverConfig, ResolverOpts) {
        (ResolverConfig::quad9_tls(), ResolverOpts::default())
    }
}


