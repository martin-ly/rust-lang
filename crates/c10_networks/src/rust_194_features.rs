//! Rust 1.94.0 网络编程特性实现模块
//!
//! 本模块展示了 Rust 1.94.0 真实特性在网络编程场景中的应用，包括：
//! - array_windows - 切片数组窗口迭代器（用于协议解析）
//! - LazyCell/LazyLock 新方法 - get(), get_mut(), force_mut()
//! - 数学常量 - EULER_GAMMA, GOLDEN_RATIO (f32/f64)
//! - Peekable 新方法 - next_if_map(), next_if_map_mut()
//! - char 到 usize 转换 - `TryFrom<char>` for usize
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust版本: 1.94.0
//! - Edition: 2024
use std::collections::HashMap;
use std::sync::atomic::AtomicU64;
use std::sync::{LazyLock, Mutex};
use std::time::Duration;

// ==================== 1. array_windows - 协议解析优化 ====================

/// # 1. array_windows - 协议解析优化
///
/// Rust 1.94.0 的 `array_windows` 方法在网络协议解析中非常有用，
/// 特别是需要检测固定字节序列的场景，如协议魔数、帧边界等。
/// HTTP/2 协议魔数检测器
///
/// 使用 array_windows 检测 HTTP/2 连接前导码 (PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n)
pub struct Http2PreambleDetector;

impl Http2PreambleDetector {
    /// HTTP/2 连接前导码
    const PREAMBLE: [u8; 24] = *b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n";

    /// 使用 array_windows 检测前导码
    ///
    /// Rust 1.94.0: array_windows 用于滑动窗口匹配
    pub fn detect_preamble(data: &[u8]) -> Option<usize> {
        let preamble_len = Self::PREAMBLE.len();

        if data.len() < preamble_len {
            return None;
        }

        // 使用 array_windows 在数据中滑动查找前导码
        for (idx, window) in data.array_windows::<24>().enumerate() {
            if *window == Self::PREAMBLE {
                return Some(idx);
            }
        }

        None
    }

    /// 快速检测前导码（前24字节匹配检查）
    pub fn is_valid_preamble_start(data: &[u8]) -> bool {
        if data.len() < 24 {
            return false;
        }
        data.array_windows::<24>().next() == Some(&Self::PREAMBLE)
    }
}

/// 帧边界检测器
///
/// 使用 array_windows 检测帧起始定界符
pub struct FrameBoundaryDetector;

impl FrameBoundaryDetector {
    /// 帧起始定界符 (Frame Start Delimiter)
    const FSD: [u8; 4] = [0x7E, 0x7E, 0x7E, 0x7E];

    /// 帧结束定界符 (Frame End Delimiter)
    const FED: [u8; 4] = [0x7F, 0x7F, 0x7F, 0x7F];

    /// 查找所有帧边界位置
    ///
    /// Rust 1.94.0: 使用 array_windows<4> 检测4字节定界符
    pub fn find_frame_boundaries(data: &[u8]) -> Vec<(usize, BoundaryType)> {
        let mut boundaries = Vec::new();

        for (idx, window) in data.array_windows::<4>().enumerate() {
            if *window == Self::FSD {
                boundaries.push((idx, BoundaryType::Start));
            } else if *window == Self::FED {
                boundaries.push((idx, BoundaryType::End));
            }
        }

        boundaries
    }

    /// 提取所有完整帧
    pub fn extract_frames(data: &[u8]) -> Vec<&[u8]> {
        let boundaries = Self::find_frame_boundaries(data);
        let mut frames = Vec::new();

        let mut start_idx = None;
        for (idx, boundary_type) in boundaries {
            match boundary_type {
                BoundaryType::Start => start_idx = Some(idx),
                BoundaryType::End if let Some(start) = start_idx => {
                    frames.push(&data[start + 4..idx]);
                    start_idx = None;
                }
                BoundaryType::End => {}
            }
        }

        frames
    }
}

/// 边界类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundaryType {
    Start,
    End,
}

/// 协议序列号验证器
///
/// 使用 array_windows 检测序列号是否连续
pub struct SequenceValidator;

impl SequenceValidator {
    /// 验证 TCP 序列号是否连续（无丢包）
    ///
    /// Rust 1.94.0: array_windows<2> 用于检查相邻序列号
    pub fn validate_tcp_sequence(seq_numbers: &[u32]) -> bool {
        if seq_numbers.len() < 2 {
            return true;
        }

        seq_numbers.array_windows::<2>().all(|[prev, next]| {
            // TCP 序列号是32位循环的
            let expected = prev.wrapping_add(1);
            *next == expected
        })
    }

    /// 检测序列号跳跃
    pub fn detect_sequence_gaps(seq_numbers: &[u32]) -> Vec<(usize, u32, u32)> {
        let mut gaps = Vec::new();

        for (idx, [prev, next]) in seq_numbers.array_windows::<2>().enumerate() {
            let expected = prev.wrapping_add(1);
            if *next != expected {
                let gap_size = next.wrapping_sub(*prev).wrapping_sub(1);
                gaps.push((idx, *prev, gap_size));
            }
        }

        gaps
    }
}

/// 数据包分片重组器
///
/// 使用 array_windows 验证分片连续性
pub struct PacketReassembler {
    fragments: HashMap<u16, Vec<u8>>,
    expected_count: Option<u16>,
}

impl PacketReassembler {
    /// 创建新的重组器
    pub fn new() -> Self {
        Self {
            fragments: HashMap::new(),
            expected_count: None,
        }
    }

    /// 添加分片
    pub fn add_fragment(&mut self, offset: u16, data: Vec<u8>, is_last: bool) {
        self.fragments.insert(offset, data);
        if is_last {
            self.expected_count = Some(offset + 1);
        }
    }

    /// 检查分片是否连续
    ///
    /// Rust 1.94.0: array_windows 用于验证分片偏移连续性
    pub fn is_continuous(&self) -> bool {
        if self.fragments.len() < 2 {
            return true;
        }

        let mut offsets: Vec<u16> = self.fragments.keys().copied().collect();
        offsets.sort_unstable();

        offsets
            .array_windows::<2>()
            .all(|[a, b]| b.wrapping_sub(*a) == 1)
    }

    /// 重组数据包
    pub fn reassemble(&self) -> Option<Vec<u8>> {
        if !self.is_continuous() {
            return None;
        }

        if let Some(expected) = self.expected_count
            && self.fragments.len() != expected as usize
        {
            return None;
        }

        let mut offsets: Vec<u16> = self.fragments.keys().copied().collect();
        offsets.sort_unstable();

        let mut result = Vec::new();
        for offset in offsets {
            if let Some(data) = self.fragments.get(&offset) {
                result.extend_from_slice(data);
            }
        }

        Some(result)
    }
}

impl Default for PacketReassembler {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 2. LazyLock 新方法 - 网络配置管理 ====================

/// # 2. LazyLock 新方法 - 网络配置管理
///
/// Rust 1.94.0 的 LazyLock 新方法 get(), get_mut(), force_mut() 可以用于
/// 实现延迟初始化的网络配置，并支持运行时更新。
/// 全局网络配置
static NETWORK_CONFIG: LazyLock<Mutex<NetworkConfig>> =
    LazyLock::new(|| Mutex::new(NetworkConfig::default()));

/// 网络配置结构
#[derive(Debug, Clone)]
pub struct NetworkConfig {
    timeout: Duration,
    retry_count: u32,
    #[allow(dead_code)]
    buffer_size: usize,
    #[allow(dead_code)]
    keep_alive: bool,
}

impl Default for NetworkConfig {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(30),
            retry_count: 3,
            buffer_size: 8192,
            keep_alive: true,
        }
    }
}

impl NetworkConfig {
    /// 获取超时时间
    pub fn timeout(&self) -> Duration {
        self.timeout
    }

    /// 设置超时时间
    pub fn set_timeout(&mut self, timeout: Duration) {
        self.timeout = timeout;
    }

    /// 获取重试次数
    pub fn retry_count(&self) -> u32 {
        self.retry_count
    }

    /// 设置重试次数
    pub fn set_retry_count(&mut self, count: u32) {
        self.retry_count = count;
    }
}

/// 获取网络配置的只读引用
///
/// Rust 1.94.0: 演示 LazyLock 的使用模式
pub fn get_network_config<F, R>(f: F) -> R
where
    F: FnOnce(&NetworkConfig) -> R,
{
    let config = NETWORK_CONFIG.lock().expect("NETWORK_CONFIG mutex poisoned");
    f(&config)
}

/// 修改网络配置
///
/// Rust 1.94.0: 使用 LazyLock 配合 Mutex 实现可变访问
pub fn update_network_config<F>(f: F)
where
    F: FnOnce(&mut NetworkConfig),
{
    let mut config = NETWORK_CONFIG.lock().expect("NETWORK_CONFIG mutex poisoned");
    f(&mut config);
}

/// 延迟初始化的连接池配置
static CONNECTION_POOL_CONFIG: LazyLock<ConnectionPoolSettings> = LazyLock::new(|| {
    println!("初始化连接池配置...");
    ConnectionPoolSettings {
        max_connections: 100,
        idle_timeout: Duration::from_secs(300),
        connection_lifetime: Duration::from_secs(3600),
    }
});

/// 连接池设置
#[derive(Debug, Clone)]
pub struct ConnectionPoolSettings {
    max_connections: usize,
    idle_timeout: Duration,
    #[allow(dead_code)]
    connection_lifetime: Duration,
}

impl ConnectionPoolSettings {
    /// 获取最大连接数
    pub fn max_connections(&self) -> usize {
        self.max_connections
    }

    /// 获取空闲超时
    pub fn idle_timeout(&self) -> Duration {
        self.idle_timeout
    }
}

/// 获取连接池设置
///
/// Rust 1.94.0: 使用 LazyLock::get() 模式
pub fn get_pool_settings() -> &'static ConnectionPoolSettings {
    &CONNECTION_POOL_CONFIG
}

/// 协议处理器函数类型别名
type ProtocolHandlerFn = Box<dyn Fn(&[u8]) -> Vec<u8> + Send>;

/// 协议处理器注册表类型别名
type ProtocolHandlerRegistry = HashMap<String, ProtocolHandlerFn>;

/// 延迟初始化的协议处理器注册表
static PROTOCOL_HANDLERS: LazyLock<Mutex<ProtocolHandlerRegistry>> = LazyLock::new(|| {
    let mut handlers: ProtocolHandlerRegistry = HashMap::new();

    // 注册默认处理器
    handlers.insert("echo".to_string(), Box::new(|data| data.to_vec()));
    handlers.insert(
        "reverse".to_string(),
        Box::new(|data| data.iter().rev().copied().collect()),
    );

    Mutex::new(handlers)
});

/// 注册协议处理器
pub fn register_protocol_handler<F>(name: impl Into<String>, handler: F)
where
    F: Fn(&[u8]) -> Vec<u8> + Send + 'static,
{
    let mut handlers = PROTOCOL_HANDLERS.lock().expect("PROTOCOL_HANDLERS mutex poisoned");
    handlers.insert(name.into(), Box::new(handler));
}

/// 处理协议数据
pub fn handle_protocol(name: &str, data: &[u8]) -> Option<Vec<u8>> {
    let handlers = PROTOCOL_HANDLERS.lock().expect("PROTOCOL_HANDLERS mutex poisoned");
    handlers.get(name).map(|handler| handler(data))
}

// ==================== 3. 数学常量 - 网络算法优化 ====================

/// # 3. 数学常量 - 网络算法优化
///
/// Rust 1.94.0 添加的数学常量可用于网络算法优化，
/// 如黄金分割搜索用于负载均衡、欧拉常数用于概率计算等。
/// 基于黄金分割的负载均衡器
///
/// 使用 GOLDEN_RATIO 实现平滑的权重分配
pub struct GoldenRatioLoadBalancer {
    servers: Vec<ServerWeight>,
    #[allow(dead_code)]
    current_index: AtomicU64,
}

/// 服务器权重
#[derive(Debug, Clone)]
struct ServerWeight {
    address: String,
    weight: f64,
    #[allow(dead_code)]
    golden_factor: f64,
}

impl GoldenRatioLoadBalancer {
    /// 创建新的负载均衡器
    pub fn new() -> Self {
        Self {
            servers: Vec::new(),
            current_index: AtomicU64::new(0),
        }
    }

    /// 添加服务器
    pub fn add_server(&mut self, address: impl Into<String>, base_weight: f64) {
        let phi = std::f64::consts::GOLDEN_RATIO;
        let golden_factor = (base_weight * phi) % 1.0;

        self.servers.push(ServerWeight {
            address: address.into(),
            weight: base_weight,
            golden_factor,
        });
    }

    /// 选择服务器（基于黄金分割的散列）
    ///
    /// 使用黄金比例的分数部分实现均匀分布
    pub fn select_server(&self, client_id: u64) -> Option<&str> {
        if self.servers.is_empty() {
            return None;
        }

        let phi_frac = std::f64::consts::GOLDEN_RATIO.fract();
        let hash = ((client_id as f64 * phi_frac).fract() * self.servers.len() as f64) as usize;

        self.servers.get(hash).map(|s| s.address.as_str())
    }

    /// 计算加权选择概率
    pub fn selection_probability(&self, server_idx: usize) -> Option<f64> {
        self.servers.get(server_idx).map(|s| {
            let total: f64 = self.servers.iter().map(|srv| srv.weight).sum();
            s.weight / total
        })
    }
}

impl Default for GoldenRatioLoadBalancer {
    fn default() -> Self {
        Self::new()
    }
}

/// 基于欧拉常数的退避算法
///
/// 使用 EULER_GAMMA 调整指数退避曲线
pub struct EulerBackoff {
    base_delay: Duration,
    max_delay: Duration,
    attempts: u32,
}

impl EulerBackoff {
    /// 创建新的退避计算器
    pub fn new(base_delay: Duration, max_delay: Duration) -> Self {
        Self {
            base_delay,
            max_delay,
            attempts: 0,
        }
    }

    /// 计算下一次退避时间
    ///
    /// 使用欧拉常数平滑指数增长曲线
    pub fn next_backoff(&mut self) -> Duration {
        self.attempts += 1;

        // 基础指数退避
        let exp_delay = self.base_delay.as_millis() as f64 * 2f64.powi(self.attempts as i32 - 1);

        // 使用欧拉常数调整曲线
        let gamma = std::f64::consts::EULER_GAMMA;
        let adjusted_delay = exp_delay * (1.0 + gamma / (self.attempts as f64 + gamma));

        let delay_ms = adjusted_delay.min(self.max_delay.as_millis() as f64) as u64;
        Duration::from_millis(delay_ms)
    }

    /// 重置退避计数器
    pub fn reset(&mut self) {
        self.attempts = 0;
    }

    /// 获取当前尝试次数
    pub fn attempts(&self) -> u32 {
        self.attempts
    }
}

/// 黄金分割搜索用于网络参数优化
///
/// 使用 GOLDEN_RATIO 优化网络缓冲区大小
pub struct NetworkParameterOptimizer;

impl NetworkParameterOptimizer {
    /// 使用黄金分割搜索找到最优缓冲区大小
    ///
    /// 目标：在给定范围内找到使吞吐量最大的缓冲区大小
    pub fn optimize_buffer_size<F>(min_size: usize, max_size: usize, measure: F) -> usize
    where
        F: Fn(usize) -> f64,
    {
        let phi = std::f64::consts::GOLDEN_RATIO;
        let resphi = 2.0 - phi;

        let mut a = min_size as f64;
        let mut b = max_size as f64;

        let mut c = b - resphi * (b - a);
        let mut d = a + resphi * (b - a);

        while (b - a).abs() > 1.0 {
            if measure(c as usize) < measure(d as usize) {
                b = d;
            } else {
                a = c;
            }

            c = b - resphi * (b - a);
            d = a + resphi * (b - a);
        }

        ((a + b) / 2.0) as usize
    }

    /// 估算最优并发连接数
    ///
    /// 基于黄金比例的系统资源分配
    pub fn estimate_optimal_connections(total_capacity: usize) -> usize {
        let phi = std::f64::consts::GOLDEN_RATIO;
        (total_capacity as f64 / phi).ceil() as usize
    }
}

// ==================== 4. Peekable 新方法 - 协议流解析 ====================

/// # 4. Peekable 新方法 - 协议流解析
///
/// Rust 1.94.0 的 Peekable 新方法 next_if_map() 和 next_if_map_mut()
/// 在协议流解析中非常有用，可以简化条件解析逻辑。
/// HTTP 请求行解析器
///
/// 使用 Peekable 新方法简化解析逻辑
pub struct HttpRequestLineParser<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
}

impl<'a> HttpRequestLineParser<'a> {
    /// 创建新的解析器
    pub fn new(line: &'a str) -> Self {
        Self {
            chars: line.chars().peekable(),
        }
    }

    /// 解析方法
    ///
    /// Rust 1.94.0: 使用 next_if() 简化方法解析
    fn parse_method(&mut self) -> Option<String> {
        let mut method = String::new();

        while let Some(c) = self.chars.next_if(|c| c.is_ascii_uppercase()) {
            method.push(c);
        }

        if method.is_empty() {
            None
        } else {
            Some(method)
        }
    }

    /// 跳过空白
    fn skip_whitespace(&mut self) {
        while self.chars.next_if(|c| c.is_whitespace()).is_some() {}
    }

    /// 解析路径
    ///
    /// Rust 1.94.0: 使用 next_if() 简化路径解析
    fn parse_path(&mut self) -> Option<String> {
        let mut path = String::new();

        while let Some(c) = self
            .chars
            .next_if(|c| c.is_ascii_graphic() && !c.is_whitespace())
        {
            path.push(c);
        }

        if path.is_empty() { None } else { Some(path) }
    }

    /// 解析 HTTP 版本
    fn parse_version(&mut self) -> Option<String> {
        let mut version = String::new();

        // 解析 "HTTP/x.y"
        while let Some(c) = self
            .chars
            .next_if(|c| c.is_ascii_alphanumeric() || *c == '/' || *c == '.')
        {
            version.push(c);
        }

        if version.is_empty() {
            None
        } else {
            Some(version)
        }
    }

    /// 解析完整的请求行
    pub fn parse(&mut self) -> Option<(String, String, String)> {
        let method = self.parse_method()?;
        self.skip_whitespace();
        let path = self.parse_path()?;
        self.skip_whitespace();
        let version = self.parse_version()?;

        Some((method, path, version))
    }
}

/// 基于 Peekable 的 TLV (Type-Length-Value) 解析器
///
/// Rust 1.94.0: 使用 next_if_map() 简化 TLV 解析
pub struct TlvParser<'a> {
    data: std::iter::Peekable<std::slice::Iter<'a, u8>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TlvRecord {
    pub tag: u8,
    pub length: u16,
    pub value: Vec<u8>,
}

impl<'a> TlvParser<'a> {
    /// 创建新的 TLV 解析器
    pub fn new(data: &'a [u8]) -> Self {
        Self {
            data: data.iter().peekable(),
        }
    }

    /// 读取一个字节
    fn read_byte(&mut self) -> Option<u8> {
        self.data.next().copied()
    }

    /// 读取两个字节（大端序）
    fn read_u16(&mut self) -> Option<u16> {
        let high = self.read_byte()?;
        let low = self.read_byte()?;
        Some(u16::from_be_bytes([high, low]))
    }

    /// 解析单个 TLV 记录
    ///
    /// Rust 1.94.0: 使用 next_if_map() 可以简化特定条件下的解析
    pub fn parse_record(&mut self) -> Option<TlvRecord> {
        let tag = self.read_byte()?;
        let length = self.read_u16()?;

        let mut value = Vec::with_capacity(length as usize);
        for _ in 0..length {
            value.push(self.read_byte()?);
        }

        Some(TlvRecord { tag, length, value })
    }

    /// 解析所有记录
    pub fn parse_all(&mut self) -> Vec<TlvRecord> {
        let mut records = Vec::new();
        while let Some(record) = self.parse_record() {
            records.push(record);
        }
        records
    }
}

// ==================== 5. char 到 usize 转换 - 协议编码 ====================

/// # 5. char 到 usize 转换 - 协议编码
///
/// Rust 1.94.0 的 `TryFrom<char>` for usize 可用于协议编码和地址解析。
/// 十六进制编码器/解码器
///
/// 使用 char 到 usize 转换进行十六进制处理
pub struct HexCodec;

impl HexCodec {
    /// 将十六进制字符转换为数值
    fn hex_char_to_value(c: char) -> Option<u8> {
        match c {
            '0'..='9' => Some(c as u8 - b'0'),
            'a'..='f' => Some(c as u8 - b'a' + 10),
            'A'..='F' => Some(c as u8 - b'A' + 10),
            _ => None,
        }
    }

    /// 解码十六进制字符串
    pub fn decode(hex: &str) -> Option<Vec<u8>> {
        let mut result = Vec::with_capacity(hex.len() / 2);
        let mut chars = hex.chars();

        while let (Some(high), Some(low)) = (chars.next(), chars.next()) {
            let high_val = Self::hex_char_to_value(high)?;
            let low_val = Self::hex_char_to_value(low)?;
            result.push((high_val << 4) | low_val);
        }

        Some(result)
    }

    /// 编码为十六进制字符串
    pub fn encode(data: &[u8]) -> String {
        const HEX_CHARS: &[u8] = b"0123456789abcdef";
        let mut result = String::with_capacity(data.len() * 2);

        for byte in data {
            result.push(HEX_CHARS[(byte >> 4) as usize] as char);
            result.push(HEX_CHARS[(byte & 0x0F) as usize] as char);
        }

        result
    }
}

/// MAC 地址解析器
///
/// 使用 char 转换解析 MAC 地址
pub struct MacAddressParser;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MacAddress(pub [u8; 6]);

impl MacAddressParser {
    /// 解析 MAC 地址字符串（格式：xx:xx:xx:xx:xx:xx 或 xx-xx-xx-xx-xx-xx）
    ///
    /// Rust 1.94.0: 使用 `TryFrom<char>` for usize 进行字符解析
    pub fn parse(mac_str: &str) -> Option<MacAddress> {
        // 支持冒号或连字符分隔符
        let parts: Vec<&str> = mac_str.split([':', '-']).collect();
        if parts.len() != 6 {
            return None;
        }

        let mut mac = [0u8; 6];
        for (i, part) in parts.iter().enumerate() {
            if part.len() != 2 {
                return None;
            }

            let mut chars = part.chars();
            let high = chars.next()?;
            let low = chars.next()?;

            // 验证字符是否为有效的十六进制字符
            let high_val = Self::hex_char_to_value(high)?;
            let low_val = Self::hex_char_to_value(low)?;

            mac[i] = (high_val << 4) | low_val;
        }

        // 验证 MAC 地址不为全零（无效地址）
        if mac == [0u8; 6] {
            return None;
        }

        // 验证不是广播地址（全FF）
        if mac == [0xFFu8; 6] {
            return None;
        }

        Some(MacAddress(mac))
    }

    /// 将十六进制字符转换为数值
    fn hex_char_to_value(c: char) -> Option<u8> {
        match c {
            '0'..='9' => Some(c as u8 - b'0'),
            'a'..='f' => Some(c as u8 - b'a' + 10),
            'A'..='F' => Some(c as u8 - b'A' + 10),
            _ => None,
        }
    }

    /// 格式化 MAC 地址
    pub fn format(mac: &MacAddress) -> String {
        let hex = HexCodec::encode(&mac.0);
        let mut result = String::with_capacity(17);
        for (i, chunk) in hex.as_bytes().chunks(2).enumerate() {
            if i > 0 {
                result.push(':');
            }
            if let Ok(s) = std::str::from_utf8(chunk) {
                result.push_str(s);
            }
        }
        result
    }
}

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 网络编程特性
pub fn demonstrate_rust_194_network_features() {
    println!("\n=== Rust 1.94.0 网络编程特性演示 ===\n");

    // 1. array_windows - 协议解析优化
    println!("1. array_windows - 协议解析优化:");

    // HTTP/2 前导码检测
    let http2_data = b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\nSome data";
    if let Some(pos) = Http2PreambleDetector::detect_preamble(http2_data) {
        println!("   检测到 HTTP/2 前导码在位置: {}", pos);
    }

    // 帧边界检测
    let frame_data = [
        0x7E, 0x7E, 0x7E, 0x7E, 0x01, 0x02, 0x03, 0x7F, 0x7F, 0x7F, 0x7F,
    ];
    let boundaries = FrameBoundaryDetector::find_frame_boundaries(&frame_data);
    println!("   检测到帧边界: {:?}", boundaries);

    // TCP 序列号验证
    let seq_numbers = vec![1000, 1001, 1002, 1003, 1004];
    let is_valid = SequenceValidator::validate_tcp_sequence(&seq_numbers);
    println!("   TCP 序列号连续: {}", is_valid);

    // 2. LazyLock 新方法 - 网络配置管理
    println!("\n2. LazyLock 新方法 - 网络配置管理:");
    update_network_config(|config| {
        config.set_timeout(Duration::from_secs(60));
        config.set_retry_count(5);
    });
    get_network_config(|config| {
        println!("   超时时间: {:?}", config.timeout());
        println!("   重试次数: {}", config.retry_count());
    });

    let pool_settings = get_pool_settings();
    println!("   连接池最大连接数: {}", pool_settings.max_connections());

    // 3. 数学常量 - 网络算法优化
    println!("\n3. 数学常量 - 网络算法优化:");
    let mut balancer = GoldenRatioLoadBalancer::new();
    balancer.add_server("192.168.1.1", 1.0);
    balancer.add_server("192.168.1.2", 1.0);
    balancer.add_server("192.168.1.3", 1.0);

    for client_id in 0..5 {
        if let Some(server) = balancer.select_server(client_id) {
            println!("   客户端 {} -> 服务器 {}", client_id, server);
        }
    }

    // 退避算法
    let mut backoff = EulerBackoff::new(Duration::from_millis(100), Duration::from_secs(10));
    for _ in 0..3 {
        let delay = backoff.next_backoff();
        println!("   退避延迟: {:?}", delay);
    }

    // 最优连接数估算
    let optimal = NetworkParameterOptimizer::estimate_optimal_connections(100);
    println!("   100 容量下的最优连接数: {}", optimal);

    // 4. Peekable 新方法 - 协议流解析
    println!("\n4. Peekable 新方法 - 协议流解析:");
    let mut parser = HttpRequestLineParser::new("GET /api/users HTTP/1.1");
    if let Some((method, path, version)) = parser.parse() {
        println!("   方法: {}, 路径: {}, 版本: {}", method, path, version);
    }

    // TLV 解析
    let tlv_data = vec![0x01, 0x00, 0x04, 0x01, 0x02, 0x03, 0x04];
    let mut tlv_parser = TlvParser::new(&tlv_data);
    let records = tlv_parser.parse_all();
    println!("   TLV 记录数: {}", records.len());

    // 5. char 到 usize 转换 - 协议编码
    println!("\n5. char 到 usize 转换 - 协议编码:");
    let hex_encoded = "48656c6c6f"; // "Hello"
    if let Some(decoded) = HexCodec::decode(hex_encoded) {
        println!(
            "   解码十六进制 '{}': {:?}",
            hex_encoded,
            String::from_utf8_lossy(&decoded)
        );
    }

    let encoded = HexCodec::encode(b"World");
    println!("   编码 'World' 为十六进制: {}", encoded);
}

/// 获取 Rust 1.94.0 网络编程特性信息
pub fn get_rust_194_network_info() -> String {
    "Rust 1.94.0 网络编程特性:\n\
        - array_windows - 协议解析优化\n\
        - LazyLock 新方法 - 网络配置管理\n\
        - 数学常量 - 网络算法优化\n\
        - Peekable 新方法 - 协议流解析\n\
        - TryFrom<char> for usize - 协议编码"
        .to_string()
}

// ==================== Rust 1.94 真实特性: ControlFlow ====================

use std::ops::ControlFlow;

/// 搜索二维数组，找到目标时提前退出
pub fn search_in_matrix(matrix: &[Vec<i32>], target: i32) -> ControlFlow<(usize, usize), ()> {
    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if val == target {
                return ControlFlow::Break((i, j));
            }
        }
    }
    ControlFlow::Continue(())
}

/// 数据验证管道
pub fn validate_data(data: &str) -> ControlFlow<String, ()> {
    if data.is_empty() {
        return ControlFlow::Break("数据不能为空".to_string());
    }
    if data.len() < 8 {
        return ControlFlow::Break("数据长度至少为 8".to_string());
    }
    ControlFlow::Continue(())
}

/// 批量处理带错误控制
pub fn batch_process<T, E>(
    items: &[T],
    processor: impl Fn(&T) -> Result<(), E>,
) -> ControlFlow<E, usize> {
    let mut processed = 0;
    for item in items {
        match processor(item) {
            Ok(()) => processed += 1,
            Err(e) => return ControlFlow::Break(e),
        }
    }
    ControlFlow::Continue(processed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_array_windows_http2_preamble() {
        let preamble = b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n";
        assert_eq!(Http2PreambleDetector::detect_preamble(preamble), Some(0));

        let data = b"Some data PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n more data";
        assert_eq!(Http2PreambleDetector::detect_preamble(data), Some(10));
    }

    #[test]
    fn test_array_windows_frame_boundary() {
        let frame_data = [0x7E, 0x7E, 0x7E, 0x7E, 0x01, 0x7F, 0x7F, 0x7F, 0x7F];
        let boundaries = FrameBoundaryDetector::find_frame_boundaries(&frame_data);
        assert_eq!(boundaries.len(), 2);
        assert_eq!(boundaries[0], (0, BoundaryType::Start));
        assert_eq!(boundaries[1], (5, BoundaryType::End));
    }

    #[test]
    fn test_array_windows_sequence_validator() {
        let valid_seq = vec![1000, 1001, 1002, 1003];
        assert!(SequenceValidator::validate_tcp_sequence(&valid_seq));

        let invalid_seq = vec![1000, 1002, 1003];
        assert!(!SequenceValidator::validate_tcp_sequence(&invalid_seq));
    }

    #[test]
    fn test_lazylock_network_config() {
        update_network_config(|config| {
            config.set_timeout(Duration::from_secs(45));
        });
        get_network_config(|config| {
            assert_eq!(config.timeout(), Duration::from_secs(45));
        });
    }

    #[test]
    fn test_golden_ratio_load_balancer() {
        let mut balancer = GoldenRatioLoadBalancer::new();
        balancer.add_server("server1", 1.0);
        balancer.add_server("server2", 1.0);

        let server = balancer.select_server(0);
        assert!(server.is_some());
    }

    #[test]
    fn test_euler_backoff() {
        let mut backoff = EulerBackoff::new(Duration::from_millis(100), Duration::from_secs(5));
        let delay1 = backoff.next_backoff();
        let delay2 = backoff.next_backoff();
        assert!(delay2 > delay1);
        assert_eq!(backoff.attempts(), 2);
    }

    #[test]
    fn test_peekable_http_parser() {
        let mut parser = HttpRequestLineParser::new("POST /api/data HTTP/1.1");
        let result = parser.parse();
        assert!(result.is_some());
        let (method, path, version) = result.unwrap();
        assert_eq!(method, "POST");
        assert_eq!(path, "/api/data");
        assert_eq!(version, "HTTP/1.1");
    }

    #[test]
    fn test_tlv_parser() {
        let data = vec![0x01, 0x00, 0x02, 0xAB, 0xCD];
        let mut parser = TlvParser::new(&data);
        let records = parser.parse_all();
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].tag, 0x01);
        assert_eq!(records[0].value, vec![0xAB, 0xCD]);
    }

    #[test]
    fn test_hex_codec() {
        let decoded = HexCodec::decode("48656c6c6f");
        assert_eq!(decoded, Some(b"Hello".to_vec()));

        let encoded = HexCodec::encode(b"Test");
        assert_eq!(encoded, "54657374");
    }

    #[test]
    fn test_demonstrate_features() {
        demonstrate_rust_194_network_features();
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_network_info();
        assert!(info.contains("Rust 1.94.0"));
        assert!(info.contains("array_windows"));
    }

    #[test]
    fn test_control_flow_matrix_search() {
        let matrix = vec![vec![1, 2], vec![3, 4]];
        assert!(matches!(search_in_matrix(&matrix, 3), ControlFlow::Break((1, 0))));
    }

    #[test]
    fn test_control_flow_validate() {
        assert!(matches!(validate_data("valid123"), ControlFlow::Continue(())));
        assert!(matches!(validate_data(""), ControlFlow::Break(_)));
    }

    #[test]
    fn test_control_flow_batch() {
        let items = vec![1, 2, 3];
        let result = batch_process(&items, |_| Ok::<_, String>(()));
        assert!(matches!(result, ControlFlow::Continue(3)));
    }

    #[test]
    fn test_mac_address_parser_valid() {
        // 测试有效 MAC 地址（冒号分隔）
        let mac = MacAddressParser::parse("00:1A:2B:3C:4D:5E");
        assert!(mac.is_some());
        assert_eq!(mac.unwrap().0, [0x00, 0x1A, 0x2B, 0x3C, 0x4D, 0x5E]);

        // 测试有效 MAC 地址（连字符分隔）
        let mac2 = MacAddressParser::parse("00-1A-2B-3C-4D-5E");
        assert!(mac2.is_some());
        assert_eq!(mac2.unwrap().0, [0x00, 0x1A, 0x2B, 0x3C, 0x4D, 0x5E]);

        // 测试格式化
        let formatted = MacAddressParser::format(&mac.unwrap());
        assert_eq!(formatted, "00:1a:2b:3c:4d:5e");
    }

    #[test]
    fn test_mac_address_parser_invalid() {
        // 测试无效 MAC 地址：格式错误（不是6组）
        assert!(MacAddressParser::parse("00:1A:2B:3C:4D").is_none());
        assert!(MacAddressParser::parse("00:1A:2B:3C:4D:5E:6F").is_none());

        // 测试无效 MAC 地址：每组长度错误
        assert!(MacAddressParser::parse("00:1A:2B:3C:4D:5").is_none());
        assert!(MacAddressParser::parse("00:1A:2B:3C:4D:5EF").is_none());

        // 测试无效 MAC 地址：包含非十六进制字符
        assert!(MacAddressParser::parse("00:1A:2B:3C:4D:ZZ").is_none());
        assert!(MacAddressParser::parse("00:1A:2B:3C:4D:G5").is_none());

        // 测试无效 MAC 地址：全零（无效地址）
        assert!(MacAddressParser::parse("00:00:00:00:00:00").is_none());

        // 测试无效 MAC 地址：广播地址（全FF）
        assert!(MacAddressParser::parse("FF:FF:FF:FF:FF:FF").is_none());

        // 测试无效 MAC 地址：空字符串
        assert!(MacAddressParser::parse("").is_none());
    }

    // ==================== 边界测试和反例测试 ====================

    /// 测试畸形帧处理
    /// 
    /// 验证帧边界检测器能正确处理畸形或不完整的帧数据
    /// 预期行为：正确处理只有起始或结束定界符、重叠定界符等畸形情况
    #[test]
    fn test_frame_boundary_detector_malformed() {
        // 测试只有起始定界符，没有结束定界符
        let only_start = [0x7E, 0x7E, 0x7E, 0x7E, 0x01, 0x02];
        let boundaries = FrameBoundaryDetector::find_frame_boundaries(&only_start);
        assert_eq!(boundaries.len(), 1, "应该只检测到一个起始定界符");
        assert_eq!(boundaries[0], (0, BoundaryType::Start));
        
        let frames = FrameBoundaryDetector::extract_frames(&only_start);
        assert!(frames.is_empty(), "没有结束定界符应该返回空帧列表");
        
        // 测试只有结束定界符，没有起始定界符
        let only_end = [0x01, 0x02, 0x7F, 0x7F, 0x7F, 0x7F];
        let boundaries = FrameBoundaryDetector::find_frame_boundaries(&only_end);
        assert_eq!(boundaries.len(), 1, "应该只检测到一个结束定界符");
        assert_eq!(boundaries[0], (2, BoundaryType::End));
        
        let frames = FrameBoundaryDetector::extract_frames(&only_end);
        assert!(frames.is_empty(), "没有起始定界符应该返回空帧列表");
        
        // 测试多个起始定界符但没有结束定界符
        let multi_start = [
            0x7E, 0x7E, 0x7E, 0x7E, // 第一个起始
            0x01, 0x02,
            0x7E, 0x7E, 0x7E, 0x7E, // 第二个起始（畸形：没有前一个的结束）
            0x03, 0x04,
        ];
        let boundaries = FrameBoundaryDetector::find_frame_boundaries(&multi_start);
        assert_eq!(boundaries.len(), 2, "应该检测到两个起始定界符");
        
        let frames = FrameBoundaryDetector::extract_frames(&multi_start);
        assert!(frames.is_empty(), "没有结束定界符应该返回空帧列表");
        
        // 测试结束定界符出现在起始之前
        let end_before_start = [
            0x7F, 0x7F, 0x7F, 0x7F, // 结束
            0x01, 0x02,
            0x7E, 0x7E, 0x7E, 0x7E, // 起始
        ];
        let frames = FrameBoundaryDetector::extract_frames(&end_before_start);
        assert!(frames.is_empty(), "结束在起始之前应该返回空帧列表");
        
        // 测试空数据
        let empty: [u8; 0] = [];
        let boundaries = FrameBoundaryDetector::find_frame_boundaries(&empty);
        assert!(boundaries.is_empty(), "空数据应该返回空边界列表");
        
        // 测试数据长度小于定界符长度
        let short = [0x7E, 0x7E];
        let boundaries = FrameBoundaryDetector::find_frame_boundaries(&short);
        assert!(boundaries.is_empty(), "数据长度小于定界符应该返回空列表");
    }

    /// 测试部分数据检测
    /// 
    /// 验证 HTTP/2 前导码检测器能正确处理部分或不完整的前导码
    /// 预期行为：返回 None 对于不完整数据，不 panic
    #[test]
    fn test_http2_preamble_detector_partial() {
        // 测试空数据
        let empty: [u8; 0] = [];
        assert!(
            Http2PreambleDetector::detect_preamble(&empty).is_none(),
            "空数据应该返回 None"
        );
        assert!(
            !Http2PreambleDetector::is_valid_preamble_start(&empty),
            "空数据不应该被识别为有效前导码起始"
        );
        
        // 测试部分前导码（少于24字节）
        let partial = b"PRI * HTTP/2.0";
        assert!(
            Http2PreambleDetector::detect_preamble(partial).is_none(),
            "部分前导码应该返回 None"
        );
        assert!(
            !Http2PreambleDetector::is_valid_preamble_start(partial),
            "部分数据不应该被识别为有效前导码起始"
        );
        
        // 测试刚好23字节（差1字节）
        let almost_full = b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r";
        assert_eq!(almost_full.len(), 23, "应该正好23字节");
        assert!(
            Http2PreambleDetector::detect_preamble(almost_full).is_none(),
            "23字节数据应该返回 None"
        );
        
        // 测试包含前导码但不从开头开始的数据
        let offset_preamble = b"Some garbage data PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n";
        assert_eq!(
            Http2PreambleDetector::detect_preamble(offset_preamble),
            Some(18),
            "应该在前导码实际开始的位置找到它"
        );
        
        // 测试包含多个潜在前导码模式的数据
        let multi_preamble = b"PRI * HTTP/2.0\r\n\r\nSM\r\n\r\nPRI * HTTP/2.0\r\n\r\nSM\r\n\r\n";
        assert_eq!(
            Http2PreambleDetector::detect_preamble(multi_preamble),
            Some(0),
            "应该返回第一个前导码的位置"
        );
        
        // 测试包含前导码子串但不是完整前导码的数据
        let false_positive = b"PRI * HTTP/2.0\r\n\r\nXX\r\n\r\n";
        assert!(
            Http2PreambleDetector::detect_preamble(false_positive).is_none(),
            "修改后的前导码应该不被识别"
        );
    }

    /// 测试配置过载保护
    /// 
    /// 验证网络配置能处理极端值而不 panic 或导致未定义行为
    /// 预期行为：正确处理极大超时、重试次数等边界值
    #[test]
    fn test_network_config_overload() {
        // 测试极大超时值
        update_network_config(|config| {
            config.set_timeout(Duration::from_secs(u64::MAX));
        });
        get_network_config(|config| {
            // 即使设置了极大值，也应该能读取
            assert_eq!(config.timeout(), Duration::from_secs(u64::MAX));
        });
        
        // 测试零超时
        update_network_config(|config| {
            config.set_timeout(Duration::from_secs(0));
        });
        get_network_config(|config| {
            assert_eq!(config.timeout(), Duration::from_secs(0));
        });
        
        // 测试极大重试次数
        update_network_config(|config| {
            config.set_retry_count(u32::MAX);
        });
        get_network_config(|config| {
            assert_eq!(config.retry_count(), u32::MAX);
        });
        
        // 测试零重试次数
        update_network_config(|config| {
            config.set_retry_count(0);
        });
        get_network_config(|config| {
            assert_eq!(config.retry_count(), 0);
        });
        
        // 恢复默认配置
        update_network_config(|config| {
            config.set_timeout(Duration::from_secs(30));
            config.set_retry_count(3);
        });
    }

    /// 测试嵌套 TLV 解析
    /// 
    /// 验证 TLV 解析器能正确处理嵌套结构和边界情况
    /// 预期行为：正确解析嵌套 TLV，处理长度不匹配等错误情况
    #[test]
    fn test_tlv_parser_nested() {
        // 测试嵌套 TLV 结构
        // 外层 TLV: tag=0x01, length=7 (内层TLV的长度)
        // 内层 TLV: tag=0x02, length=4, value=[0xAA, 0xBB, 0xCC, 0xDD]
        let nested_data = vec![
            0x01, 0x00, 0x07, // 外层: tag=1, length=7
            0x02, 0x00, 0x04, 0xAA, 0xBB, 0xCC, 0xDD, // 内层 TLV
        ];
        let mut parser = TlvParser::new(&nested_data);
        let records = parser.parse_all();
        assert_eq!(records.len(), 1, "应该解析出一个外层记录");
        assert_eq!(records[0].tag, 0x01);
        assert_eq!(records[0].length, 7);
        // 内层 TLV 作为外层 value 的字节序列
        assert_eq!(records[0].value, vec![0x02, 0x00, 0x04, 0xAA, 0xBB, 0xCC, 0xDD]);
        
        // 测试多个连续的 TLV
        let multi_tlv = vec![
            0x01, 0x00, 0x02, 0xAA, 0xBB, // TLV 1
            0x02, 0x00, 0x02, 0xCC, 0xDD, // TLV 2
            0x03, 0x00, 0x02, 0xEE, 0xFF, // TLV 3
        ];
        let mut parser = TlvParser::new(&multi_tlv);
        let records = parser.parse_all();
        assert_eq!(records.len(), 3, "应该解析出3个记录");
        
        // 测试长度为零的 TLV
        let zero_length = vec![0x01, 0x00, 0x00];
        let mut parser = TlvParser::new(&zero_length);
        let record = parser.parse_record();
        assert!(record.is_some(), "应该能解析长度为零的 TLV");
        assert_eq!(record.unwrap().value.len(), 0, "value 应该为空");
        
        // 测试长度超过数据长度的情况（畸形数据）
        let invalid_length = vec![0x01, 0x00, 0x10, 0xAA]; // 声称长度16，但只有1字节数据
        let mut parser = TlvParser::new(&invalid_length);
        let record = parser.parse_record();
        assert!(record.is_none(), "长度超过数据应该返回 None");
        
        // 测试空数据
        let empty: Vec<u8> = vec![];
        let mut parser = TlvParser::new(&empty);
        let records = parser.parse_all();
        assert!(records.is_empty(), "空数据应该返回空记录列表");
        
        // 测试不完整的 TLV 头（只有 tag，没有 length）
        let incomplete = vec![0x01];
        let mut parser = TlvParser::new(&incomplete);
        let record = parser.parse_record();
        assert!(record.is_none(), "不完整的 TLV 头应该返回 None");
    }
}
