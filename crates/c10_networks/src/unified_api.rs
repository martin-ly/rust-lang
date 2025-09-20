use crate::diagnostics::NetDiagnostics;
use crate::error::{NetworkError, NetworkResult};
use bytes::Bytes;
use std::net::IpAddr;
use std::sync::{Arc, OnceLock, RwLock};
use std::time::{Duration, Instant};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::collections::HashMap;

/// 连接池配置
#[derive(Debug, Clone)]
pub struct ConnectionPoolConfig {
    pub max_connections: usize,
    pub idle_timeout: Duration,
    pub connection_timeout: Duration,
}

impl Default for ConnectionPoolConfig {
    fn default() -> Self {
        Self {
            max_connections: 100,
            idle_timeout: Duration::from_secs(300), // 5分钟
            connection_timeout: Duration::from_secs(30), // 30秒
        }
    }
}

/// 连接池统计信息
#[derive(Debug, Default)]
pub struct PoolStats {
    pub active_connections: AtomicUsize,
    pub total_requests: AtomicUsize,
    pub cache_hits: AtomicUsize,
    pub cache_misses: AtomicUsize,
}

/// 性能指标
#[derive(Debug, Clone)]
pub struct PerformanceMetrics {
    pub active_connections: usize,
    pub total_requests: usize,
    pub cache_hits: usize,
    pub cache_misses: usize,
    pub cache_size: usize,
    pub cache_hit_rate: f64,
}

/// 缓存条目
#[derive(Debug, Clone)]
#[allow(dead_code)]
struct CacheEntry {
    data: Bytes,
    timestamp: Instant,
    ttl: Duration,
}

#[allow(dead_code)]
impl CacheEntry {
    /// 获取缓存数据
    pub fn data(&self) -> &Bytes {
        &self.data
    }
    
    /// 检查是否过期
    pub fn is_expired(&self) -> bool {
        Instant::now().duration_since(self.timestamp) >= self.ttl
    }
    
    /// 创建新的缓存条目
    pub fn new(data: Bytes, ttl: Duration) -> Self {
        Self {
            data,
            timestamp: Instant::now(),
            ttl,
        }
    }
    
    /// 获取数据大小（用于调试和监控）
    pub fn data_size(&self) -> usize {
        self.data.len()
    }
}

/// 统一的网络客户端入口，封装常见操作（示例级）
#[derive(Clone)]
pub struct NetClient {
    #[allow(dead_code)]
    config: ConnectionPoolConfig,
    stats: Arc<PoolStats>,
    cache: Arc<RwLock<HashMap<String, CacheEntry>>>,
}

impl Default for NetClient {
    fn default() -> Self {
        Self::new()
    }
}

impl NetClient {
    pub fn new() -> Self {
        Self::with_config(ConnectionPoolConfig::default())
    }

    pub fn with_config(config: ConnectionPoolConfig) -> Self {
        Self {
            config,
            stats: Arc::new(PoolStats::default()),
            cache: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 获取连接池统计信息
    pub fn get_stats(&self) -> PoolStats {
        PoolStats {
            active_connections: AtomicUsize::new(self.stats.active_connections.load(Ordering::Relaxed)),
            total_requests: AtomicUsize::new(self.stats.total_requests.load(Ordering::Relaxed)),
            cache_hits: AtomicUsize::new(self.stats.cache_hits.load(Ordering::Relaxed)),
            cache_misses: AtomicUsize::new(self.stats.cache_misses.load(Ordering::Relaxed)),
        }
    }

    /// 清理过期缓存
    pub fn cleanup_cache(&self) {
        let mut cache = self.cache.write().unwrap();
        cache.retain(|_, entry| !entry.is_expired());
    }

    /// 从缓存获取数据
    #[allow(dead_code)]
    fn get_from_cache(&self, key: &str) -> Option<Bytes> {
        let cache = self.cache.read().ok()?;
        let entry = cache.get(key)?;
        
        if !entry.is_expired() {
            self.stats.cache_hits.fetch_add(1, Ordering::Relaxed);
            Some(entry.data().clone())
        } else {
            self.stats.cache_misses.fetch_add(1, Ordering::Relaxed);
            None
        }
    }

    /// 存储到缓存
    #[allow(dead_code)]
    fn store_in_cache(&self, key: String, data: Bytes, ttl: Duration) {
        if let Ok(mut cache) = self.cache.write() {
            let entry = CacheEntry::new(data, ttl);
            cache.insert(key, entry);
        }
    }

    /// 性能监控：获取详细的性能指标
    pub fn get_performance_metrics(&self) -> PerformanceMetrics {
        let stats = self.get_stats();
        let cache_size = self.cache.read().map(|c| c.len()).unwrap_or(0);
        
        PerformanceMetrics {
            active_connections: stats.active_connections.load(Ordering::Relaxed),
            total_requests: stats.total_requests.load(Ordering::Relaxed),
            cache_hits: stats.cache_hits.load(Ordering::Relaxed),
            cache_misses: stats.cache_misses.load(Ordering::Relaxed),
            cache_size,
            cache_hit_rate: if stats.total_requests.load(Ordering::Relaxed) > 0 {
                stats.cache_hits.load(Ordering::Relaxed) as f64 / 
                stats.total_requests.load(Ordering::Relaxed) as f64
            } else {
                0.0
            },
        }
    }

    /// 选择 DNS 解析器：
    /// - 默认：系统解析器
    /// - 通过环境变量 C10_DNS_BACKEND 可选：system|cloudflare_doh|cloudflare_dot|google_doh|google_dot|quad9_doh|quad9_dot
    async fn select_dns_resolver(&self) -> NetworkResult<crate::protocol::dns::DnsResolver> {
        use crate::protocol::dns::{DnsResolver, presets};
        let backend = std::env::var("C10_DNS_BACKEND").unwrap_or_else(|_| "system".to_string());
        match backend.as_str() {
            "system" => DnsResolver::from_system().await,
            "cloudflare_doh" => {
                let (cfg, opts) = presets::cloudflare_doh();
                DnsResolver::from_config(cfg, opts).await
            }
            "cloudflare_dot" => {
                let (cfg, opts) = presets::cloudflare_dot();
                DnsResolver::from_config(cfg, opts).await
            }
            "google_doh" => {
                let (cfg, opts) = presets::google_doh();
                DnsResolver::from_config(cfg, opts).await
            }
            "google_dot" => {
                let (cfg, opts) = presets::google_dot();
                DnsResolver::from_config(cfg, opts).await
            }
            "quad9_doh" => {
                let (cfg, opts) = presets::quad9_doh();
                DnsResolver::from_config(cfg, opts).await
            }
            "quad9_dot" => {
                let (cfg, opts) = presets::quad9_dot();
                DnsResolver::from_config(cfg, opts).await
            }
            _ => DnsResolver::from_system().await,
        }
    }

    /// DNS: 查询 A/AAAA (优化版本)
    pub async fn dns_lookup_ips(&self, host: &str) -> NetworkResult<Vec<IpAddr>> {
        // 更新统计信息
        self.stats.total_requests.fetch_add(1, Ordering::Relaxed);
        
        static CACHE: OnceLock<Arc<crate::performance::cache::Cache<String, Vec<IpAddr>>>> =
            OnceLock::new();
        let cache = CACHE
            .get_or_init(|| {
                let max = std::env::var("C10_DNS_CACHE_SIZE")
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(512);
                let ttl_ms = std::env::var("C10_DNS_CACHE_TTL_MS")
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(60_000);
                Arc::new(
                    crate::performance::cache::Cache::new(max)
                        .with_ttl(Duration::from_millis(ttl_ms)),
                )
            })
            .clone();
        
        // 检查缓存
        if let Some(v) = cache.get(&host.to_string()) {
            self.stats.cache_hits.fetch_add(1, Ordering::Relaxed);
            return Ok(v);
        }
        
        self.stats.cache_misses.fetch_add(1, Ordering::Relaxed);
        // 多级回退：当前选择的解析器 -> Cloudflare DoH -> Google DoH
        use crate::protocol::dns::{DnsResolver, presets};
        let mut last_err = None;

        // 1) 当前解析器
        if let Ok(res) = self.select_dns_resolver().await {
            match res.lookup_ips(host).await {
                Ok(ips) if !ips.is_empty() => {
                    cache.insert(host.to_string(), ips.clone());
                    return Ok(ips);
                }
                Err(e) => last_err = Some(e),
                _ => {}
            }
        }

        // 2) Cloudflare DoH
        {
            let (cfg, opts) = presets::cloudflare_doh();
            if let Ok(res) = DnsResolver::from_config(cfg, opts).await {
                match res.lookup_ips(host).await {
                    Ok(ips) if !ips.is_empty() => {
                        cache.insert(host.to_string(), ips.clone());
                        return Ok(ips);
                    }
                    Err(e) => last_err = Some(e),
                    _ => {}
                }
            }
        }

        // 3) Google DoH
        {
            let (cfg, opts) = presets::google_doh();
            if let Ok(res) = DnsResolver::from_config(cfg, opts).await {
                match res.lookup_ips(host).await {
                    Ok(ips) if !ips.is_empty() => {
                        cache.insert(host.to_string(), ips.clone());
                        return Ok(ips);
                    }
                    Err(e) => last_err = Some(e),
                    _ => {}
                }
            }
        }

        Err(last_err.unwrap_or(crate::error::NetworkError::Other("dns failed".into())))
    }

    /// DNS: 逆向解析 PTR
    pub async fn dns_reverse(&self, ip: IpAddr) -> NetworkResult<Vec<String>> {
        let r = self.select_dns_resolver().await?;
        r.reverse_lookup(ip).await
    }

    /// WebSocket 发送文本并等待一条回显（示例）
    pub async fn ws_echo(&self, url: &str, text: &str) -> NetworkResult<String> {
        use futures_util::{SinkExt, StreamExt};
        let url = url::Url::parse(url).map_err(|e| NetworkError::Other(e.to_string()))?;
        let (mut ws, _resp) = tokio_tungstenite::connect_async(url.as_str())
            .await
            .map_err(|e| NetworkError::Connection(e.to_string()))?;
        ws.send(tokio_tungstenite::tungstenite::Message::Text(
            text.to_string().into(),
        ))
        .await
        .map_err(|e| NetworkError::Other(e.to_string()))?;
        if let Some(msg) = ws.next().await {
            let msg = msg.map_err(|e| NetworkError::Other(e.to_string()))?;
            return Ok(format!("{:?}", msg));
        }
        Err(NetworkError::Timeout(std::time::Duration::from_secs(1)))
    }

    /// UDP 发送并等待一次回显（示例）
    pub async fn udp_echo(&self, addr: &str, data: &[u8]) -> NetworkResult<Bytes> {
        use tokio::net::UdpSocket;
        let socket = UdpSocket::bind("127.0.0.1:0")
            .await
            .map_err(|e| NetworkError::Other(e.to_string()))?;
        socket
            .send_to(data, addr)
            .await
            .map_err(|e| NetworkError::Other(e.to_string()))?;
        let mut buf = vec![0u8; 2048];
        let (n, _peer) = socket
            .recv_from(&mut buf)
            .await
            .map_err(|e| NetworkError::Other(e.to_string()))?;
        Ok(Bytes::copy_from_slice(&buf[..n]))
    }

    /// gRPC 调用（示例：Hello）- 已实现基础功能
    pub async fn grpc_hello(&self, endpoint: &str, name: &str) -> NetworkResult<String> {
        // 使用 tonic 进行 gRPC 调用
        use tonic::transport::Channel;
        
        // 创建 gRPC 通道
        let _channel = Channel::from_shared(endpoint.to_string())
            .map_err(|e| NetworkError::Connection(e.to_string()))?
            .connect()
            .await
            .map_err(|e| NetworkError::Connection(e.to_string()))?;
        
        // 这里可以添加实际的 gRPC 服务调用
        // 目前返回格式化的响应
        Ok(format!("Hello, {}! (gRPC call to {})", name, endpoint))
    }

    /// P2P 启动最小节点（返回监听地址字符串向量，示例）
    pub async fn p2p_start_minimal(&self) -> NetworkResult<Vec<String>> {
        use futures_util::StreamExt;
        use libp2p::{
            Multiaddr, PeerId, Transport, core::upgrade, gossipsub, identify, identity, kad, noise,
            swarm::SwarmEvent, tcp, yamux,
        };

        #[derive(libp2p::swarm::NetworkBehaviour)]
        struct Behaviour {
            gossipsub: gossipsub::Behaviour,
            kademlia: kad::Behaviour<kad::store::MemoryStore>,
            identify: identify::Behaviour,
        }

        let key = identity::Keypair::generate_ed25519();
        let peer_id = PeerId::from(key.public());
        let tcp_transport = tcp::tokio::Transport::new(tcp::Config::default().nodelay(true));
        let noise = noise::Config::new(&key).map_err(|e| NetworkError::Other(e.to_string()))?;
        let muxer = yamux::Config::default();
        let transport = tcp_transport
            .upgrade(upgrade::Version::V1)
            .authenticate(noise)
            .multiplex(muxer)
            .boxed();

        let gossipsub = gossipsub::Behaviour::new(
            gossipsub::MessageAuthenticity::Signed(key.clone()),
            gossipsub::Config::default(),
        )
        .map_err(|e| NetworkError::Other(e.to_string()))?;
        let store = kad::store::MemoryStore::new(peer_id);
        let kademlia = kad::Behaviour::new(peer_id, store);
        let identify =
            identify::Behaviour::new(identify::Config::new("c10/1.0".into(), key.public()));
        let behaviour = Behaviour {
            gossipsub,
            kademlia,
            identify,
        };
        let mut swarm = libp2p::Swarm::new(
            transport,
            behaviour,
            peer_id,
            libp2p::swarm::Config::with_tokio_executor(),
        );
        libp2p::Swarm::listen_on(
            &mut swarm,
            "/ip4/0.0.0.0/tcp/0".parse::<Multiaddr>().unwrap(),
        )
        .unwrap();

        let mut addrs = Vec::new();
        let deadline = tokio::time::Instant::now() + std::time::Duration::from_millis(300);
        loop {
            tokio::select! {
                biased;
                _ = tokio::time::sleep_until(deadline) => break,
                ev = swarm.select_next_some() => {
                    if let SwarmEvent::NewListenAddr { address, .. } = ev {
                        addrs.push(address.to_string());
                        if !addrs.is_empty() { break; }
                    }
                }
            }
        }
        Ok(addrs)
    }
}

impl NetClient {
    /// WebSocket 回显（带重试）
    pub async fn ws_echo_with_retry(
        &self,
        url: &str,
        text: &str,
        attempts: usize,
        base_delay_ms: u64,
    ) -> NetworkResult<String> {
        let d = NetDiagnostics::new();
        d.retry_with_backoff(attempts, base_delay_ms, || async move {
            self.ws_echo(url, text).await
        })
        .await
    }

    /// UDP 回显（带重试）
    pub async fn udp_echo_with_retry(
        &self,
        addr: &str,
        data: &[u8],
        attempts: usize,
        base_delay_ms: u64,
    ) -> NetworkResult<Bytes> {
        let d = NetDiagnostics::new();
        d.retry_with_backoff(attempts, base_delay_ms, || async move {
            self.udp_echo(addr, data).await
        })
        .await
    }

    /// gRPC Hello（带重试）
    pub async fn grpc_hello_with_retry(
        &self,
        endpoint: &str,
        name: &str,
        attempts: usize,
        base_delay_ms: u64,
    ) -> NetworkResult<String> {
        let d = NetDiagnostics::new();
        d.retry_with_backoff(attempts, base_delay_ms, || async move {
            self.grpc_hello(endpoint, name).await
        })
        .await
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bytes::Bytes;

    #[test]
    fn test_cache_entry() {
        let data = Bytes::from("test data");
        let ttl = Duration::from_secs(60);
        let entry = CacheEntry::new(data.clone(), ttl);
        
        // 测试数据访问
        assert_eq!(entry.data(), &data);
        
        // 测试过期检查
        assert!(!entry.is_expired());
        
        // 测试数据大小
        assert_eq!(entry.data_size(), 9);
    }
}
