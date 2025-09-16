use crate::error::{NetworkError, NetworkResult};
use crate::diagnostics::NetDiagnostics;
use bytes::Bytes;
use std::net::IpAddr;
use std::sync::{Arc, OnceLock};
use std::time::Duration;

/// 统一的网络客户端入口，封装常见操作（示例级）
#[derive(Clone, Default)]
pub struct NetClient;

impl NetClient {
    pub fn new() -> Self { Self }

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

    /// DNS: 查询 A/AAAA
    pub async fn dns_lookup_ips(&self, host: &str) -> NetworkResult<Vec<IpAddr>> {
        static CACHE: OnceLock<Arc<crate::performance::cache::Cache<String, Vec<IpAddr>>>> = OnceLock::new();
        let cache = CACHE.get_or_init(|| {
            let max = std::env::var("C10_DNS_CACHE_SIZE").ok().and_then(|s| s.parse().ok()).unwrap_or(512);
            let ttl_ms = std::env::var("C10_DNS_CACHE_TTL_MS").ok().and_then(|s| s.parse().ok()).unwrap_or(60_000);
            Arc::new(crate::performance::cache::Cache::new(max).with_ttl(Duration::from_millis(ttl_ms)))
        }).clone();
        if let Some(v) = cache.get(&host.to_string()) { return Ok(v); }
        // 多级回退：当前选择的解析器 -> Cloudflare DoH -> Google DoH
        use crate::protocol::dns::{presets, DnsResolver};
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
        ws.send(tokio_tungstenite::tungstenite::Message::Text(text.to_string().into()))
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
        let socket = UdpSocket::bind("127.0.0.1:0").await.map_err(|e| NetworkError::Other(e.to_string()))?;
        socket.send_to(data, addr).await.map_err(|e| NetworkError::Other(e.to_string()))?;
        let mut buf = vec![0u8; 2048];
        let (n, _peer) = socket.recv_from(&mut buf).await.map_err(|e| NetworkError::Other(e.to_string()))?;
        Ok(Bytes::copy_from_slice(&buf[..n]))
    }

    /// gRPC 调用（示例：Hello）- 暂时禁用，需要正确的 tonic-build 配置
    pub async fn grpc_hello(&self, _endpoint: &str, name: &str) -> NetworkResult<String> {
        // TODO: 需要正确配置 tonic-build 来生成 gRPC 服务代码
        // 目前只返回一个模拟响应
        Ok(format!("Hello, {}! (gRPC service temporarily disabled)", name))
    }

    /// P2P 启动最小节点（返回监听地址字符串向量，示例）
    pub async fn p2p_start_minimal(&self) -> NetworkResult<Vec<String>> {
        use libp2p::{core::upgrade, gossipsub, identify, identity, kad, noise, tcp, yamux, Multiaddr, PeerId, Transport, swarm::SwarmEvent};
        use futures_util::StreamExt;

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
        let transport = tcp_transport.upgrade(upgrade::Version::V1).authenticate(noise).multiplex(muxer).boxed();

        let gossipsub = gossipsub::Behaviour::new(
            gossipsub::MessageAuthenticity::Signed(key.clone()),
            gossipsub::Config::default(),
        ).map_err(|e| NetworkError::Other(e.to_string()))?;
        let store = kad::store::MemoryStore::new(peer_id);
        let kademlia = kad::Behaviour::new(peer_id, store);
        let identify = identify::Behaviour::new(identify::Config::new("c10/1.0".into(), key.public()));
        let behaviour = Behaviour { gossipsub, kademlia, identify };
        let mut swarm = libp2p::Swarm::new(transport, behaviour, peer_id, libp2p::swarm::Config::with_tokio_executor());
        libp2p::Swarm::listen_on(&mut swarm, "/ip4/0.0.0.0/tcp/0".parse::<Multiaddr>().unwrap()).unwrap();

        let mut addrs = Vec::new();
        let deadline = tokio::time::Instant::now() + std::time::Duration::from_millis(300);
        loop {
            tokio::select! {
                biased;
                _ = tokio::time::sleep_until(deadline) => break,
                ev = swarm.select_next_some() => {
                    if let SwarmEvent::NewListenAddr { address, .. } = ev {
                        addrs.push(address.to_string());
                        if addrs.len() >= 1 { break; }
                    }
                }
            }
        }
        Ok(addrs)
    }
}

impl NetClient {
    /// WebSocket 回显（带重试）
    pub async fn ws_echo_with_retry(&self, url: &str, text: &str, attempts: usize, base_delay_ms: u64) -> NetworkResult<String> {
        let d = NetDiagnostics::new();
        d.retry_with_backoff(attempts, base_delay_ms, || async move {
            self.ws_echo(url, text).await
        }).await
    }

    /// UDP 回显（带重试）
    pub async fn udp_echo_with_retry(&self, addr: &str, data: &[u8], attempts: usize, base_delay_ms: u64) -> NetworkResult<Bytes> {
        let d = NetDiagnostics::new();
        d.retry_with_backoff(attempts, base_delay_ms, || async move {
            self.udp_echo(addr, data).await
        }).await
    }

    /// gRPC Hello（带重试）
    pub async fn grpc_hello_with_retry(&self, endpoint: &str, name: &str, attempts: usize, base_delay_ms: u64) -> NetworkResult<String> {
        let d = NetDiagnostics::new();
        d.retry_with_backoff(attempts, base_delay_ms, || async move {
            self.grpc_hello(endpoint, name).await
        }).await
    }
}


