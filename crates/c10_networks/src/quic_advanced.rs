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
        let key_der = PrivateKeyDer::Pkcs8(cert.signing_key.serialize_der().into());

        Ok((vec![cert_der], key_der))
    }

    /// 加载 PEM 格式证书
    pub fn load_certs_from_pem(cert_pem: &[u8]) -> Result<Vec<CertificateDer<'static>>, String> {
        use rustls::pki_types::pem::PemObject;
        let certs: Vec<_> = CertificateDer::pem_slice_iter(cert_pem)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| format!("cert parse: {}", e))?;
        if certs.is_empty() {
            return Err("no certificates found".to_string());
        }
        Ok(certs)
    }

    /// 解析 SocketAddr 字符串
    pub fn parse_socket_addr(addr: &str) -> Result<SocketAddr, String> {
        addr.parse::<SocketAddr>()
            .map_err(|e| format!("parse socket addr: {}", e))
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
            println!(
                "QUIC server listening on {}",
                self.endpoint.local_addr().map_err(|e| e.to_string())?
            );

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
    async fn handle_stream(mut send: SendStream, mut recv: RecvStream) -> Result<(), String> {
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

    // =====================================================================
    // 5. QUIC 高级特性
    // =====================================================================

    /// QUIC 高级特性：不可靠数据报、0-RTT、连接迁移
    ///
    /// 本模块展示 quinn 0.11 提供的超越基础 Echo 的高级 QUIC 能力。
    /// 所有代码均为概念骨架，展示 API 的正确使用方式。
    pub mod quic_advanced_features {
        #![forbid(unsafe_code)]

        use bytes::Bytes;
        use quinn::{Connecting, Connection, ZeroRttAccepted};
        use std::net::SocketAddr;
        use std::time::Duration;
        use tokio::time::interval;

        // -----------------------------------------------------------------
        // 5.1 Datagram (不可靠传输)
        // -----------------------------------------------------------------

        /// QUIC Datagram —— 不可靠、无顺序保证的应用层数据报
        ///
        /// 适合场景：
        /// - 游戏状态同步（位置、朝向，丢帧可容忍）
        /// - 实时音视频（RTP over QUIC）
        /// - 高频遥测上报（允许部分丢失）
        ///
        /// 与流(Stream)的区别：
        /// | 特性 | Stream | Datagram |
        /// |------|--------|----------|
        /// | 可靠性 | 可靠、有序 | 不可靠、无序 |
        /// | 分片 | 自动 | 须单包容纳 |
        /// | 流控 | 有 | 无 |
        /// | 拥塞控制 | 有（不丢弃）| 有（可丢弃旧报）|
        pub struct UnreliableDatagramChannel {
            connection: Connection,
        }

        impl UnreliableDatagramChannel {
            /// 基于已有连接创建数据报通道
            pub fn new(connection: Connection) -> Self {
                Self { connection }
            }

            /// 发送不可靠数据报
            ///
            /// 数据须小于 `max_datagram_size()`，否则返回 `TooLarge` 错误。
            /// 若发送缓冲区满，旧数据报可能被丢弃（按 FIFO）。
            pub fn send(&self, data: &[u8]) -> Result<(), quinn::SendDatagramError> {
                self.connection.send_datagram(Bytes::copy_from_slice(data))
            }

            /// 异步发送（等待拥塞窗口，优先保留旧数据报）
            pub async fn send_wait(&self, data: &[u8]) -> Result<(), quinn::SendDatagramError> {
                self.connection
                    .send_datagram_wait(Bytes::copy_from_slice(data))
                    .await
            }

            /// 接收一个数据报
            pub async fn recv(&self) -> Result<Bytes, quinn::ConnectionError> {
                self.connection.read_datagram().await
            }

            /// 当前可发送的最大数据报尺寸
            pub fn max_size(&self) -> Option<usize> {
                self.connection.max_datagram_size()
            }

            /// 发送缓冲区剩余空间
            pub fn send_buffer_space(&self) -> usize {
                self.connection.datagram_send_buffer_space()
            }
        }

        // -----------------------------------------------------------------
        // 5.2 0-RTT (Zero Round Trip Time)
        // -----------------------------------------------------------------

        /// 0-RTT —— 会话恢复时的零往返延迟
        ///
        /// QUIC 基于 TLS 1.3 的会话恢复机制，允许客户端在首次握手中附带应用数据，
        /// 将延迟从 1-RTT 降至 0-RTT。
        ///
        /// 安全警告：
        /// - 0-RTT 数据可能被重放攻击，因此只能用于幂等操作。
        /// - 服务器可能拒绝 0-RTT，此时数据不会送达。
        ///
        /// quinn API 说明：
        /// - 客户端：`Connecting::into_0rtt()` 在持有先前会话票据时返回 `Ok`。
        ///   返回的 `ZeroRttAccepted` Future 在握手完成后解析为 `bool`：
        ///   `true` 表示服务器接受了 0-RTT，`false` 表示被拒绝。
        /// - 服务器：`Incoming::accept()` 得到 `Connecting` 后，`into_0rtt()` 总是返回
        ///   `Ok`（即 0.5-RTT），且 `ZeroRttAccepted` 永远解析为 `true`。
        pub struct ZeroRttSession;

        impl ZeroRttSession {
            /// 客户端尝试 0-RTT 发送
            ///
            /// 须在 `ClientConfig` 中配置会话恢复（如 rustls 的 `enable_early_data`）。
            pub fn client_try_0rtt(
                connecting: Connecting,
            ) -> Result<(Connection, ZeroRttAccepted), Box<Connecting>> {
                connecting.into_0rtt().map_err(Box::new)
            }

            /// 服务器接受 0.5-RTT 连接
            ///
            /// 服务器端可在握手完成前就开始发送数据（0.5-RTT）。
            pub fn server_accept_0rtt(
                connecting: Connecting,
            ) -> Result<(Connection, ZeroRttAccepted), Box<Connecting>> {
                // 服务器端总是成功
                connecting.into_0rtt().map_err(Box::new)
            }

            /// 检查 0-RTT 是否最终被接受
            pub async fn check_accepted(accepted: ZeroRttAccepted) -> bool {
                accepted.await
            }
        }

        // -----------------------------------------------------------------
        // 5.3 Connection Migration (连接迁移)
        // -----------------------------------------------------------------

        /// 连接迁移 —— WiFi ↔ 蜂窝网络无缝切换
        ///
        /// QUIC 使用连接 ID 而非四元组（源IP、源端口、目的IP、目的端口）标识连接，
        /// 因此客户端 IP/端口变化不会导致连接中断。
        ///
        /// quinn 0.11 API 现状：
        /// - `ServerConfig::migration(true)` 默认已启用，协议层自动处理 PATH_CHALLENGE/RESPONSE。
        /// - `Connection::remote_address()` 会在迁移完成后返回新地址。
        /// - **quinn 目前不暴露应用层迁移事件**（如 `on_path_changed` 回调），
        ///   应用只能通过轮询 `remote_address()` 或观察 RTT 变化间接感知。
        ///
        /// 若需更细粒度的路径控制，可考虑 `quinn-proto` 底层 API。
        pub struct ConnectionMigrationMonitor {
            connection: Connection,
        }

        impl ConnectionMigrationMonitor {
            /// 创建迁移监控器
            pub fn new(connection: Connection) -> Self {
                Self { connection }
            }

            /// 轮询检测地址是否发生变化
            ///
            /// 返回 `(old, new)` 若检测到变更。
            pub async fn watch_address_change(
                &self,
                check_interval: Duration,
            ) -> (SocketAddr, SocketAddr) {
                let initial = self.connection.remote_address();
                let mut ticker = interval(check_interval);
                loop {
                    ticker.tick().await;
                    let current = self.connection.remote_address();
                    if current != initial {
                        return (initial, current);
                    }
                }
            }

            /// 获取当前对端地址
            pub fn current_remote_address(&self) -> SocketAddr {
                self.connection.remote_address()
            }

            /// 获取当前连接 RTT（可用于判断路径质量）
            pub fn current_rtt(&self) -> Duration {
                self.connection.rtt()
            }

            /// 获取连接统计信息
            pub fn stats(&self) -> quinn::ConnectionStats {
                self.connection.stats()
            }
        }

        // -----------------------------------------------------------------
        // 5.4 配置结构体（用于编译期测试与参数传递）
        // -----------------------------------------------------------------

        /// 数据报配置
        #[derive(Debug, Clone, PartialEq, Eq)]
        pub struct DatagramConfig {
            max_size: usize,
            enabled: bool,
        }

        impl DatagramConfig {
            /// 创建数据报配置
            pub fn new(max_size: usize, enabled: bool) -> Self {
                Self { max_size, enabled }
            }

            /// 获取最大数据报尺寸
            pub fn max_size(&self) -> usize {
                self.max_size
            }

            /// 是否启用数据报
            pub fn enabled(&self) -> bool {
                self.enabled
            }
        }

        /// 0-RTT 配置
        #[derive(Debug, Clone, PartialEq, Eq)]
        pub struct ZeroRttConfig {
            enabled: bool,
            max_early_data: usize,
        }

        impl ZeroRttConfig {
            /// 创建 0-RTT 配置
            pub fn new(enabled: bool, max_early_data: usize) -> Self {
                Self {
                    enabled,
                    max_early_data,
                }
            }

            /// 是否启用 0-RTT
            pub fn enabled(&self) -> bool {
                self.enabled
            }

            /// 获取最大早期数据量
            pub fn max_early_data(&self) -> usize {
                self.max_early_data
            }
        }

        /// 连接迁移配置
        #[derive(Debug, Clone, PartialEq, Eq)]
        pub struct MigrationConfig {
            enabled: bool,
            idle_timeout_ms: u64,
        }

        impl MigrationConfig {
            /// 创建连接迁移配置
            pub fn new(enabled: bool, idle_timeout_ms: u64) -> Self {
                Self {
                    enabled,
                    idle_timeout_ms,
                }
            }

            /// 是否启用连接迁移
            pub fn enabled(&self) -> bool {
                self.enabled
            }

            /// 获取空闲超时时间（毫秒）
            pub fn idle_timeout_ms(&self) -> u64 {
                self.idle_timeout_ms
            }
        }

        // -----------------------------------------------------------------
        // Tests
        // -----------------------------------------------------------------

        #[cfg(test)]
        mod tests {
            use super::*;

            /// 验证 Datagram API 类型签名正确
            #[test]
            fn test_datagram_api_surface() {
                fn _assert_send(
                    c: &Connection,
                    data: &[u8],
                ) -> Result<(), quinn::SendDatagramError> {
                    c.send_datagram(Bytes::copy_from_slice(data))
                }
                fn _assert_recv(c: &Connection) -> quinn::ReadDatagram<'_> {
                    c.read_datagram()
                }
                fn _assert_max_size(c: &Connection) -> Option<usize> {
                    c.max_datagram_size()
                }

                let _ = _assert_send as fn(&Connection, &[u8]) -> _;
                let _ = _assert_max_size as fn(&Connection) -> _;
                // `_assert_recv` 返回带有生命周期的 `ReadDatagram<'_>`，无法做裸函数指针转换，
                // 此处仅验证其定义可被编译器接受即可。
                let _ = _assert_recv;
            }

            /// 验证 0-RTT API 类型签名正确
            #[test]
            fn test_zero_rtt_api_surface() {
                fn _assert_into_0rtt(
                    c: Connecting,
                ) -> Result<(Connection, ZeroRttAccepted), Box<Connecting>> {
                    c.into_0rtt().map_err(Box::new)
                }
                let _ = _assert_into_0rtt as fn(Connecting) -> _;
            }

            /// 验证连接迁移相关 API 存在
            #[test]
            fn test_migration_api_surface() {
                fn _assert_remote_address(c: &Connection) -> SocketAddr {
                    c.remote_address()
                }
                fn _assert_rtt(c: &Connection) -> Duration {
                    c.rtt()
                }
                let _ = _assert_remote_address as fn(&Connection) -> _;
                let _ = _assert_rtt as fn(&Connection) -> _;
            }

            /// 验证结构体可实例化（需要 Connection，故用 PhantomData 做编译检查）
            #[test]
            fn test_structs_compilable() {
                let _ = std::marker::PhantomData::<UnreliableDatagramChannel>;
                let _ = std::marker::PhantomData::<ConnectionMigrationMonitor>;
                let _ = ZeroRttSession;
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use std::net::SocketAddr;

        /// 测试生成自签名证书成功并返回非空数据
        #[test]
        fn test_generate_self_signed_cert_ok() {
            let (certs, key) = generate_self_signed_cert(vec!["localhost".to_string()]).unwrap();
            assert!(!certs.is_empty(), "证书列表不应为空");
            assert!(!certs[0].is_empty(), "证书数据不应为空");

            let key_bytes = match &key {
                PrivateKeyDer::Pkcs8(k) => k.secret_pkcs8_der(),
                _ => panic!("unexpected key type"),
            };
            assert!(!key_bytes.is_empty(), "私钥数据不应为空");
        }

        /// 测试空主题别名时生成证书不 panic
        #[test]
        fn test_generate_self_signed_cert_empty_sans() {
            let result = generate_self_signed_cert(vec![]);
            // rcgen 0.13 允许空列表，行为视实现而定，此处仅验证不 panic
            let _ = result;
        }

        /// 测试从有效 PEM 加载证书成功
        #[test]
        fn test_load_certs_from_pem_valid() {
            let cert = rcgen::generate_simple_self_signed(vec!["test.example.com".into()]).unwrap();
            let pem = cert.cert.pem();
            let loaded = load_certs_from_pem(pem.as_bytes()).unwrap();
            assert_eq!(loaded.len(), 1, "应解析出 1 张证书");
            assert!(!loaded[0].is_empty(), "加载的证书不应为空");
        }

        /// 测试加载无效 PEM 数据应返回错误
        #[test]
        fn test_load_certs_from_pem_invalid() {
            let result = load_certs_from_pem(b"this is not a pem");
            assert!(result.is_err(), "无效 PEM 应返回错误");
        }

        /// 测试加载空 PEM 数据应返回错误
        #[test]
        fn test_load_certs_from_pem_empty() {
            let result = load_certs_from_pem(b"");
            assert!(result.is_err(), "空 PEM 应返回错误");
        }

        /// 测试解析有效的 IPv4 地址
        #[test]
        fn test_parse_socket_addr_valid_ipv4() {
            let addr = parse_socket_addr("127.0.0.1:8080").unwrap();
            assert_eq!(addr, SocketAddr::from(([127, 0, 0, 1], 8080)));
        }

        /// 测试解析有效的 IPv6 地址
        #[test]
        fn test_parse_socket_addr_valid_ipv6() {
            let addr = parse_socket_addr("[::1]:443").unwrap();
            assert_eq!(addr, SocketAddr::from(([0, 0, 0, 0, 0, 0, 0, 1], 443)));
        }

        /// 测试解析无效地址应返回错误
        #[test]
        fn test_parse_socket_addr_invalid() {
            let result = parse_socket_addr("not-an-address");
            assert!(result.is_err(), "无效地址应返回错误");

            let result = parse_socket_addr("127.0.0.1");
            assert!(result.is_err(), "缺少端口应返回错误");
        }

        /// 测试 Http3OverQuicConcept 帧类型说明文本非空
        #[test]
        fn test_http3_over_quic_concept_frame_types() {
            let text = Http3OverQuicConcept::frame_types();
            assert!(!text.is_empty(), "帧类型说明不应为空");
            assert!(text.contains("HEADERS"), "应包含 HEADERS 帧说明");
        }

        /// 测试 Http3OverQuicConcept 连接迁移说明文本非空
        #[test]
        fn test_http3_over_quic_concept_migration() {
            let text = Http3OverQuicConcept::connection_migration_concept();
            assert!(!text.is_empty(), "连接迁移说明不应为空");
            assert!(
                text.contains("PATH_CHALLENGE"),
                "应包含 PATH_CHALLENGE 说明"
            );
        }

        /// 测试 DatagramConfig 创建与 getter
        #[test]
        fn test_datagram_config_creation_and_getters() {
            let cfg = quic_advanced_features::DatagramConfig::new(1200, true);
            assert_eq!(cfg.max_size(), 1200);
            assert!(cfg.enabled());
        }

        /// 测试 ZeroRttConfig 创建与 getter
        #[test]
        fn test_zero_rtt_config_creation_and_getters() {
            let cfg = quic_advanced_features::ZeroRttConfig::new(true, 65536);
            assert!(cfg.enabled());
            assert_eq!(cfg.max_early_data(), 65536);
        }

        /// 测试 MigrationConfig 创建与 getter
        #[test]
        fn test_migration_config_creation_and_getters() {
            let cfg = quic_advanced_features::MigrationConfig::new(true, 30000);
            assert!(cfg.enabled());
            assert_eq!(cfg.idle_timeout_ms(), 30000);
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

    pub mod quic_advanced_features {
        pub struct UnreliableDatagramChannel;
        pub struct ZeroRttSession;
        pub struct ConnectionMigrationMonitor;
    }
}

pub use quic_full::{quic_advanced_features, *};
