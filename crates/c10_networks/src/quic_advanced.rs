//! QUIC / HTTP3 完整实现 —— 现代安全传输协议
//!
//! # 概述
//!
//! QUIC (Quick UDP Internet Connections) 是 Google 开发、IETF 标准化的
//! 基于 UDP 的传输协议。HTTP/3 在 QUIC 之上运行，解决了 TCP+TLS+HTTP/2
//! 的队头阻塞和握手延迟问题。
//!
//! # 核心特性
//!
//! | 特性 | TCP+TLS+HTTP/2 | QUIC+HTTP/3 |
//! |------|---------------|-------------|
//! | 握手延迟 | 2-3 RTT (TCP+TLS) | 0-1 RTT (QUIC 内置 TLS 1.3) |
//! | 队头阻塞 | TCP 层阻塞所有流 | 流独立，单流丢包不影响他流 |
//! | 连接迁移 | 四元组变化需重连 | 连接 ID 标识，IP/端口变化不影响 |
//! | 拥塞控制 | 内核实现，应用不可控 | 用户态实现，可定制 |
//! | 安全性 | TLS 在传输层之上 | TLS 1.3 内置于握手 |
//!
//! # 依赖
//! - `quinn` — QUIC 协议实现
//! - `rustls` — TLS 1.3
//! - `rcgen` — 自签名证书生成（开发/测试）
//!
//! # 前置条件
//! 启用 `quic` feature: `cargo build -p c10_networks --features quic`

#[cfg(feature = "quic")]
pub mod quic_full {
    use quinn::{ClientConfig, Connection, Endpoint, RecvStream, SendStream, ServerConfig};
    use rustls::pki_types::{CertificateDer, PrivateKeyDer};
    use std::net::SocketAddr;
    use std::sync::Arc;

    // =====================================================================
    // 1. TLS 证书管理
    // =====================================================================

    /// 生成自签名证书（开发/测试用）
    ///
    /// 生产环境应使用 Let's Encrypt 或企业 CA 签发的证书。
    pub fn generate_self_signed_cert(
        subject_alt_names: Vec<String>,
    ) -> Result<(Vec<CertificateDer<'static>>, PrivateKeyDer<'static>), String> {
        let cert = rcgen::generate_simple_self_signed(subject_alt_names)
            .map_err(|e| format!("cert generation: {}", e))?;

        let cert_der = cert.cert.der().clone();
        let key_der = PrivateKeyDer::Pkcs8(cert.key_pair.serialize_der().into());

        Ok((vec![cert_der], key_der))
    }

    /// 加载 PEM 格式证书
    pub fn load_certs_from_pem(cert_pem: &[u8]) -> Result<Vec<CertificateDer<'static>>, String> {
        let mut certs = Vec::new();
        for cert in rustls_pemfile::certs(&mut &*cert_pem) {
            match cert {
                Ok(c) => certs.push(c),
                Err(e) => return Err(format!("cert parse: {}", e)),
            }
        }
        if certs.is_empty() {
            return Err("no certificates found".to_string());
        }
        Ok(certs)
    }

    // =====================================================================
    // 2. QUIC 服务器
    // =====================================================================

    /// QUIC Echo 服务器
    ///
    /// 接受连接，读取双向流中的数据，回传给客户端。
    pub struct QuicEchoServer {
        endpoint: Endpoint,
    }

    impl QuicEchoServer {
        /// 创建服务器并绑定地址
        pub fn new(bind_addr: SocketAddr) -> Result<Self, String> {
            let (cert_chain, key) = generate_self_signed_cert(vec!["localhost".into()])?;

            let mut server_config = ServerConfig::with_single_cert(cert_chain, key)
                .map_err(|e| format!("server config: {}", e))?;

            // 传输层配置
            let mut transport = quinn::TransportConfig::default();
            transport.max_concurrent_bidi_streams(100u32.into());
            transport.max_concurrent_uni_streams(100u32.into());
            server_config.transport_config(Arc::new(transport));

            let endpoint =
                Endpoint::server(server_config, bind_addr).map_err(|e| format!("bind: {}", e))?;

            Ok(Self { endpoint })
        }

        /// 运行服务器（阻塞）
        pub async fn run(&self) -> Result<(), String> {
            println!("QUIC server listening on {}", self.endpoint.local_addr().map_err(|e| e.to_string())?);

            while let Some(incoming) = self.endpoint.accept().await {
                tokio::spawn(async move {
                    match incoming.await {
                        Ok(connection) => {
                            println!("新连接: {}", connection.remote_address());
                            if let Err(e) = handle_connection(connection).await {
                                eprintln!("连接处理错误: {}", e);
                            }
                        }
                        Err(e) => {
                            eprintln!("连接建立失败: {}", e);
                        }
                    }
                });
            }

            Ok(())
        }

        pub fn local_addr(&self) -> Result<SocketAddr, String> {
            self.endpoint.local_addr().map_err(|e| e.to_string())
        }
    }

    /// 处理单个 QUIC 连接
    async fn handle_connection(connection: Connection) -> Result<(), String> {
        loop {
            // 接受双向流
            match connection.accept_bi().await {
                Ok((send, recv)) => {
                    tokio::spawn(async move {
                        if let Err(e) = handle_stream(send, recv).await {
                            eprintln!("流处理错误: {}", e);
                        }
                    });
                }
                Err(quinn::ConnectionError::ApplicationClosed(_)) => {
                    println!("连接正常关闭");
                    break;
                }
                Err(e) => {
                    eprintln!("流接受错误: {}", e);
                    break;
                }
            }
        }
        Ok(())
    }

    /// 处理单个双向流
    async fn handle_stream(
        mut send: SendStream,
        mut recv: RecvStream,
    ) -> Result<(), String> {
        let mut buf = vec![0u8; 4096];
        loop {
            match recv.read(&mut buf).await.map_err(|e| e.to_string())? {
                Some(0) => break, // 流结束
                Some(n) => {
                    // Echo 回传
                    send.write_all(&buf[..n]).await.map_err(|e| e.to_string())?;
                }
                None => break,
            }
        }
        send.finish().map_err(|e| e.to_string())?;
        Ok(())
    }

    // =====================================================================
    // 3. QUIC 客户端
    // =====================================================================

    /// QUIC Echo 客户端
    pub struct QuicEchoClient {
        endpoint: Endpoint,
    }

    impl QuicEchoClient {
        /// 创建客户端
        pub fn new() -> Result<Self, String> {
            let client_config = ClientConfig::try_with_platform_verifier()
                .map_err(|e| format!("client config: {}", e))?;

            let mut endpoint = Endpoint::client("0.0.0.0:0".parse().unwrap())
                .map_err(|e| format!("client endpoint: {}", e))?;
            endpoint.set_default_client_config(client_config);

            Ok(Self { endpoint })
        }

        /// 连接到服务器并发送数据
        pub async fn echo(
            &self,
            server_addr: SocketAddr,
            server_name: &str,
            data: &[u8],
        ) -> Result<Vec<u8>, String> {
            let connection = self
                .endpoint
                .connect(server_addr, server_name)
                .map_err(|e| format!("connect setup: {}", e))?
                .await
                .map_err(|e| format!("connect: {}", e))?;

            // 打开双向流
            let (mut send, mut recv) = connection
                .open_bi()
                .await
                .map_err(|e| format!("open stream: {}", e))?;

            // 发送数据
            send.write_all(data).await.map_err(|e| e.to_string())?;
            send.finish().map_err(|e| e.to_string())?;

            // 读取响应
            let response = recv
                .read_to_end(64 * 1024)
                .await
                .map_err(|e| e.to_string())?;

            // 显式关闭连接（ graceful ）
            connection.close(0u32.into(), b"done");

            Ok(response)
        }

        /// 0-RTT 概念性支持
        ///
        /// QUIC 支持会话恢复，实现 0-RTT 握手。
        /// 需要在首次连接后保存会话票据。
        pub async fn echo_with_0rtt(
            &self,
            _server_addr: SocketAddr,
            _server_name: &str,
            _data: &[u8],
            _session_ticket: Option<&[u8]>,
        ) -> Result<Vec<u8>, String> {
            // 实际实现需要使用 rustls 的 session resumption
            // 此处为概念占位
            Err("0-RTT requires session resumption setup (see rustls docs)".to_string())
        }
    }

    // =====================================================================
    // 4. HTTP/3 层概念
    // =====================================================================

    /// HTTP/3 与 QUIC 的关系说明
    ///
    /// HTTP/3 将 HTTP 语义映射到 QUIC 流：
    /// - 每个请求/响应对使用独立的 QUIC 双向流
    /// - 请求优先级通过 QUIC 流优先级实现
    /// - 服务器推送使用单向流
    pub struct Http3OverQuicConcept;

    impl Http3OverQuicConcept {
        /// HTTP/3 帧类型（概念性）
        pub fn frame_types() -> &'static str {
            r#"
HTTP/3 核心帧类型:
- HEADERS (0x01): 压缩的请求/响应头 (QPACK)
- DATA (0x00): 请求/响应体
- SETTINGS (0x04): 连接级配置
- GOAWAY (0x07): 优雅关闭

与 HTTP/2 的差异:
- 无优先级帧（使用 QUIC 流优先级）
- 无 WINDOW_UPDATE（QUIC 内置流控）
- 无 PING/PONG（QUIC 内置 keepalive）
"#
        }

        /// 连接迁移概念
        ///
        /// QUIC 使用连接 ID 而非四元组标识连接，支持网络切换：
        /// - WiFi → 4G 切换不断连
        /// - NAT 重绑定自动恢复
        pub fn connection_migration_concept() -> &'static str {
            r#"
QUIC 连接迁移:
1. 客户端在 new_path 上发送 PATH_CHALLENGE
2. 服务器在 new_path 上响应 PATH_RESPONSE
3. 验证成功后，流量切换到 new_path
4. old_path 保持一段时间用于包重排序

关键优势:
- IP/端口变化不影响连接
- 无需重新握手
- 零 RTT 恢复传输
"#
        }
    }
}

// =====================================================================
// 非 quic feature 的占位实现
// =====================================================================

#[cfg(not(feature = "quic"))]
pub mod quic_full {
    pub fn generate_self_signed_cert(_sans: Vec<String>) -> Result<(Vec<u8>, Vec<u8>), String> {
        Err("'quic' feature required".to_string())
    }

    pub struct QuicEchoServer;
    impl QuicEchoServer {
        pub fn new(_addr: std::net::SocketAddr) -> Result<Self, String> {
            Err("'quic' feature required".to_string())
        }
        pub async fn run(&self) -> Result<(), String> {
            Err("'quic' feature required".to_string())
        }
    }

    pub struct QuicEchoClient;
    impl QuicEchoClient {
        pub fn new() -> Result<Self, String> {
            Err("'quic' feature required".to_string())
        }
        pub async fn echo(
            &self,
            _addr: std::net::SocketAddr,
            _name: &str,
            _data: &[u8],
        ) -> Result<Vec<u8>, String> {
            Err("'quic' feature required".to_string())
        }
    }
}

pub use quic_full::*;
