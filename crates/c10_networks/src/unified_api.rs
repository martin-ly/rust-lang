use crate::error::{NetworkError, NetworkResult};
use crate::diagnostics::NetDiagnostics;
use bytes::Bytes;

/// 统一的网络客户端入口，封装常见操作（示例级）
#[derive(Clone, Default)]
pub struct NetClient;

impl NetClient {
    pub fn new() -> Self { Self }

    /// WebSocket 发送文本并等待一条回显（示例）
    pub async fn ws_echo(&self, url: &str, text: &str) -> NetworkResult<String> {
        use futures_util::{SinkExt, StreamExt};
        let url = url::Url::parse(url).map_err(|e| NetworkError::Other(e.to_string()))?;
        let (mut ws, _resp) = tokio_tungstenite::connect_async(url)
            .await
            .map_err(|e| NetworkError::Connection(e.to_string()))?;
        ws.send(tokio_tungstenite::tungstenite::Message::Text(text.to_string()))
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

    /// gRPC 调用（示例：Hello）
    pub async fn grpc_hello(&self, endpoint: &str, name: &str) -> NetworkResult<String> {
        pub mod hello { tonic::include_proto!("hello"); }
        use hello::{greeter_client::GreeterClient, HelloRequest};
        let mut client = GreeterClient::connect(endpoint.to_string())
            .await
            .map_err(|e| NetworkError::Connection(e.to_string()))?;
        let resp = client
            .say_hello(tonic::Request::new(HelloRequest { name: name.into() }))
            .await
            .map_err(|e| NetworkError::Other(e.to_string()))?;
        Ok(resp.into_inner().message)
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


