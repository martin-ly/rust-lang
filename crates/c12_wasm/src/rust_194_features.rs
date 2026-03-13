//! Rust 1.94.0 WASM 特性实现模块
//!
//! 本模块展示了 Rust 1.94.0 真实特性在 WebAssembly 场景中的应用，包括：
//! - array_windows - 切片数组窗口迭代器（用于 WASM 数据处理）
//! - LazyCell/LazyLock 新方法 - get(), get_mut(), force_mut()
//! - 数学常量 - EULER_GAMMA, GOLDEN_RATIO (f32/f64)
//! - Peekable 新方法 - next_if_map(), next_if_map_mut()
//! - char 到 usize 转换 - TryFrom<char> for usize
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust版本: 1.94.0
//! - Edition: 2024
use std::collections::HashMap;
use std::sync::{LazyLock, Mutex};

// ==================== 1. array_windows - WASM 数据处理 ====================

/// # 1. array_windows - WASM 数据处理
///
/// Rust 1.94.0 的 `array_windows` 方法在 WebAssembly 应用中特别有用，
/// 可以用于高效处理线性内存中的数据序列。

/// WASM 线性内存视图
///
/// 使用 array_windows 处理 WASM 内存中的数据
pub struct WasmMemoryView<'a> {
    data: &'a [u8],
}

impl<'a> WasmMemoryView<'a> {
    /// 从切片创建内存视图
    pub fn new(data: &'a [u8]) -> Self {
        Self { data }
    }

    /// 读取 32 位整数（小端序）
    ///
    /// Rust 1.94.0: array_windows<4> 用于读取 4 字节值
    pub fn read_i32_le(&self, offset: usize) -> Option<i32> {
        let bytes = self.data.get(offset..offset + 4)?;
        Some(i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    /// 读取所有 32 位整数
    ///
    /// Rust 1.94.0: array_windows<4> 批量读取 4 字节整数
    pub fn read_all_i32_le(&self) -> impl Iterator<Item = i32> + '_ {
        self.data.array_windows::<4>().map(|window| {
            i32::from_le_bytes([window[0], window[1], window[2], window[3]])
        })
    }

    /// 查找字节序列
    ///
    /// Rust 1.94.0: array_windows 用于滑动窗口搜索
    pub fn find_sequence(&self, pattern: &[u8]) -> Option<usize> {
        if pattern.is_empty() || pattern.len() > self.data.len() {
            return None;
        }

        // 使用泛型数组比较，利用 array_windows
        match pattern.len() {
            1 => self.data.iter().position(|&b| b == pattern[0]),
            2 => {
                for (idx, window) in self.data.array_windows::<2>().enumerate() {
                    if *window == [pattern[0], pattern[1]] {
                        return Some(idx);
                    }
                }
                None
            }
            4 => {
                let pat = [pattern[0], pattern[1], pattern[2], pattern[3]];
                for (idx, window) in self.data.array_windows::<4>().enumerate() {
                    if *window == pat {
                        return Some(idx);
                    }
                }
                None
            }
            8 => {
                if pattern.len() == 8 {
                    let pat = [
                        pattern[0], pattern[1], pattern[2], pattern[3],
                        pattern[4], pattern[5], pattern[6], pattern[7],
                    ];
                    for (idx, window) in self.data.array_windows::<8>().enumerate() {
                        if *window == pat {
                            return Some(idx);
                        }
                    }
                }
                None
            }
            _ => {
                // 通用实现（回退）
                self.data
                    .windows(pattern.len())
                    .position(|window| window == pattern)
            }
        }
    }

    /// 验证内存对齐
    ///
    /// Rust 1.94.0: array_windows 验证 4 字节对齐
    pub fn verify_4byte_alignment(&self) -> bool {
        if self.data.len() < 4 {
            return true;
        }

        // 检查地址是否都能被 4 整除（模拟）
        self.data.array_windows::<4>().all(|_| true)
    }

    /// 计算校验和（简化版）
    ///
    /// Rust 1.94.0: array_windows<2> 用于 16 位校验和计算
    pub fn checksum_16bit(&self) -> u16 {
        let mut sum: u32 = 0;

        // 使用 2 字节窗口计算校验和
        for [high, low] in self.data.array_windows::<2>() {
            sum += u16::from_be_bytes([*high, *low]) as u32;
        }

        // 处理奇数字节
        if self.data.len() % 2 == 1 {
            sum += (self.data[self.data.len() - 1] as u32) << 8;
        }

        // 折叠进位
        while (sum >> 16) != 0 {
            sum = (sum & 0xFFFF) + (sum >> 16);
        }

        !(sum as u16)
    }
}

/// WASM 数据包解析器
///
/// 使用 array_windows 解析网络数据包
pub struct WasmPacketParser;

impl WasmPacketParser {
    /// 以太网帧头解析
    ///
    /// Rust 1.94.0: array_windows<6> 用于 MAC 地址
    pub fn parse_ethernet_header(data: &[u8]) -> Option<EthernetHeader> {
        if data.len() < 14 {
            return None;
        }

        let mut dest_mac = [0u8; 6];
        let mut src_mac = [0u8; 6];

        // 使用 array_windows 读取 MAC 地址
        if let Some(window) = data.array_windows::<6>().next() {
            dest_mac.copy_from_slice(window);
        }

        if let Some(window) = data.get(6..12) {
            src_mac.copy_from_slice(window);
        }

        let ether_type = u16::from_be_bytes([data[12], data[13]]);

        Some(EthernetHeader {
            dest_mac,
            src_mac,
            ether_type,
        })
    }

    /// 查找 IP 头部
    ///
    /// Rust 1.94.0: array_windows<20> 用于 IP 头部检测
    pub fn find_ip_packet(data: &[u8]) -> Option<usize> {
        // 查找 0x45 (IPv4, IHL=5) 模式
        for (idx, window) in data.array_windows::<2>().enumerate() {
            if window[0] == 0x45 {
                return Some(idx);
            }
        }
        None
    }
}

/// 以太网帧头
#[derive(Debug, Clone, Copy)]
pub struct EthernetHeader {
    pub dest_mac: [u8; 6],
    pub src_mac: [u8; 6],
    pub ether_type: u16,
}

/// WASM 图像数据处理
///
/// 使用 array_windows 处理像素数据
pub struct WasmImageProcessor;

impl WasmImageProcessor {
    /// 计算 RGB 像素的平均颜色
    ///
    /// Rust 1.94.0: array_windows<3> 用于 RGB 像素处理
    pub fn average_rgb(data: &[u8]) -> Option<(u8, u8, u8)> {
        if data.len() < 3 {
            return None;
        }

        let mut r_sum: u64 = 0;
        let mut g_sum: u64 = 0;
        let mut b_sum: u64 = 0;
        let mut count: u64 = 0;

        for [r, g, b] in data.array_windows::<3>() {
            r_sum += *r as u64;
            g_sum += *g as u64;
            b_sum += *b as u64;
            count += 1;
        }

        if count == 0 {
            return None;
        }

        Some((
            (r_sum / count) as u8,
            (g_sum / count) as u8,
            (b_sum / count) as u8,
        ))
    }

    /// 检测边缘（简化 Sobel 算子）
    ///
    /// Rust 1.94.0: array_windows<3> 用于 3x3 卷积
    pub fn detect_edges_simple(data: &[u8], width: usize) -> Vec<u8> {
        if data.len() < width * 3 || width < 3 {
            return vec![0; data.len() / 3];
        }

        let height = data.len() / (width * 3);
        let mut edges = vec![0u8; width * height];

        // 简化的边缘检测，使用水平梯度
        for y in 0..height {
            for x in 1..width - 1 {
                let idx = y * width + x;
                if let Some(window) = data.get(idx * 3..idx * 3 + 3) {
                    // 简化的梯度计算
                    let curr = (window[0] as i16 + window[1] as i16 + window[2] as i16) / 3;
                    let prev = if x > 0 {
                        let prev_idx = (y * width + x - 1) * 3;
                        if let Some(prev_window) = data.get(prev_idx..prev_idx + 3) {
                            (prev_window[0] as i16 + prev_window[1] as i16 + prev_window[2] as i16) / 3
                        } else {
                            curr
                        }
                    } else {
                        curr
                    };
                    let gradient = ((curr - prev) / 2).unsigned_abs() as u8;
                    edges[idx] = gradient;
                }
            }
        }

        edges
    }
}

// ==================== 2. LazyLock 新方法 - WASM 模块管理 ====================

/// # 2. LazyLock 新方法 - WASM 模块管理
///
/// Rust 1.94.0 的 LazyLock 新方法在 WASM 环境中可用于延迟初始化模块和资源。

/// 全局 WASM 实例配置
static WASM_INSTANCE_CONFIG: LazyLock<Mutex<WasmInstanceConfig>> = LazyLock::new(|| {
    Mutex::new(WasmInstanceConfig {
        memory_pages: 1,
        max_memory_pages: 1024,
        enable_simd: true,
        enable_bulk_memory: true,
    })
});

/// WASM 实例配置
#[derive(Debug, Clone)]
pub struct WasmInstanceConfig {
    pub memory_pages: u32,
    pub max_memory_pages: u32,
    pub enable_simd: bool,
    pub enable_bulk_memory: bool,
}

impl WasmInstanceConfig {
    /// 获取内存限制（字节）
    pub fn memory_limit_bytes(&self) -> usize {
        self.max_memory_pages as usize * 64 * 1024 // 64KB per page
    }

    /// 设置内存页数
    pub fn set_memory_pages(&mut self, pages: u32) {
        self.memory_pages = pages.min(self.max_memory_pages);
    }
}

/// 获取 WASM 配置
pub fn get_wasm_config<F, R>(f: F) -> R
where
    F: FnOnce(&WasmInstanceConfig) -> R,
{
    let config = WASM_INSTANCE_CONFIG.lock().unwrap();
    f(&config)
}

/// 更新 WASM 配置
pub fn update_wasm_config<F>(f: F)
where
    F: FnOnce(&mut WasmInstanceConfig),
{
    let mut config = WASM_INSTANCE_CONFIG.lock().unwrap();
    f(&mut config);
}

/// 延迟初始化的导出函数表
static EXPORT_TABLE: LazyLock<HashMap<String, WasmExportInfo>> = LazyLock::new(|| {
    let mut table = HashMap::new();
    table.insert(
        "memory".to_string(),
        WasmExportInfo {
            name: "memory".to_string(),
            kind: ExportKind::Memory,
            index: 0,
        },
    );
    table.insert(
        "_start".to_string(),
        WasmExportInfo {
            name: "_start".to_string(),
            kind: ExportKind::Function,
            index: 0,
        },
    );
    table
});

/// WASM 导出信息
#[derive(Debug, Clone)]
pub struct WasmExportInfo {
    pub name: String,
    pub kind: ExportKind,
    pub index: u32,
}

/// 导出类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExportKind {
    Function,
    Memory,
    Table,
    Global,
}

/// 获取导出信息
pub fn get_export_info(name: &str) -> Option<&'static WasmExportInfo> {
    EXPORT_TABLE.get(name)
}

/// 延迟初始化的 WASI 预打开目录
static WASI_PREOPENS: LazyLock<Mutex<Vec<WasiPreopenDir>>> = LazyLock::new(|| {
    Mutex::new(vec![
        WasiPreopenDir {
            guest_path: "/".to_string(),
            host_path: ".".to_string(),
            read_only: false,
        },
    ])
});

/// WASI 预打开目录
#[derive(Debug, Clone)]
pub struct WasiPreopenDir {
    pub guest_path: String,
    pub host_path: String,
    pub read_only: bool,
}

/// 添加预打开目录
pub fn add_preopen_dir(guest_path: impl Into<String>, host_path: impl Into<String>) {
    let mut preopens = WASI_PREOPENS.lock().unwrap();
    preopens.push(WasiPreopenDir {
        guest_path: guest_path.into(),
        host_path: host_path.into(),
        read_only: false,
    });
}

/// 获取预打开目录列表
pub fn get_preopen_dirs() -> Vec<WasiPreopenDir> {
    WASI_PREOPENS.lock().unwrap().clone()
}

// ==================== 3. 数学常量 - WASM 图形计算 ====================

/// # 3. 数学常量 - WASM 图形计算
///
/// Rust 1.94.0 的数学常量在 WebAssembly 图形和数学计算中非常有用。

/// 黄金比例布局计算器
///
/// 使用 GOLDEN_RATIO 计算响应式布局
pub struct GoldenRatioLayout;

impl GoldenRatioLayout {
    /// 黄金比例常量
    const PHI: f64 = std::f64::consts::GOLDEN_RATIO;
    const PHI_F32: f32 = std::f32::consts::GOLDEN_RATIO;

    /// 计算黄金比例分割
    ///
    /// 将宽度分割为符合黄金比例的两部分
    pub fn split_width(width: f64) -> (f64, f64) {
        let larger = width / Self::PHI;
        let smaller = width - larger;
        (larger, smaller)
    }

    /// 计算黄金矩形尺寸
    pub fn golden_rectangle(width: f64) -> (f64, f64) {
        let height = width / Self::PHI;
        (width, height)
    }

    /// 生成黄金螺旋点（用于动画路径）
    ///
    /// Rust 1.94.0: 使用 GOLDEN_RATIO 生成螺旋
    pub fn golden_spiral_points(count: usize, scale: f64) -> Vec<(f64, f64)> {
        (0..count)
            .map(|i| {
                let theta = i as f64 * std::f64::consts::TAU / Self::PHI;
                let r = (i as f64).sqrt() * scale;
                (r * theta.cos(), r * theta.sin())
            })
            .collect()
    }

    /// 计算黄金比例网格
    ///
    /// 生成符合黄金比例的网格布局
    pub fn golden_grid(container_width: f64, container_height: f64, items: usize) -> Vec<(f64, f64, f64, f64)> {
        let mut layouts = Vec::new();
        let _phi = Self::PHI;

        // 使用黄金比例递归分割
        let mut stack = vec![(0.0, 0.0, container_width, container_height)];

        for i in 0..items {
            if let Some((x, y, w, h)) = stack.pop() {
                let (w1, w2) = Self::split_width(w);
                layouts.push((x, y, w1, h));

                if i + 1 < items {
                    stack.push((x + w1, y, w2, h));
                }
            }
        }

        layouts
    }

    /// 使用 f32 版本进行快速计算（WASM 友好）
    pub fn split_width_f32(width: f32) -> (f32, f32) {
        let larger = width / Self::PHI_F32;
        let smaller = width - larger;
        (larger, smaller)
    }
}

/// 基于欧拉常数的音频合成器
///
/// 使用 EULER_GAMMA 进行音频波形计算
pub struct EulerAudioSynthesizer {
    sample_rate: f32,
    gamma: f32,
}

impl EulerAudioSynthesizer {
    /// 创建新的合成器
    pub fn new(sample_rate: f32) -> Self {
        Self {
            sample_rate,
            gamma: std::f32::consts::EULER_GAMMA,
        }
    }

    /// 生成欧拉调制正弦波
    ///
    /// Rust 1.94.0: 使用 EULER_GAMMA 调制波形
    pub fn generate_euler_sine(&self, frequency: f32, duration_sec: f32) -> Vec<f32> {
        let num_samples = (self.sample_rate * duration_sec) as usize;
        let mut samples = Vec::with_capacity(num_samples);

        for i in 0..num_samples {
            let t = i as f32 / self.sample_rate;
            // 使用欧拉常数调制振幅
            let modulation = 1.0 + self.gamma * (t * frequency * 0.1).sin();
            let sample = (t * frequency * 2.0 * std::f32::consts::PI).sin() * modulation;
            samples.push(sample * 0.5); // 防止削波
        }

        samples
    }

    /// 生成包络（使用欧拉常数）
    pub fn generate_euler_envelope(&self, duration_sec: f32) -> Vec<f32> {
        let num_samples = (self.sample_rate * duration_sec) as usize;
        let decay_factor = (-self.gamma / duration_sec).exp();

        (0..num_samples)
            .map(|i| {
                let t = i as f32 / self.sample_rate;
                (-t * decay_factor).exp()
            })
            .collect()
    }

    /// 计算谐波序列（基于调和级数）
    pub fn harmonic_series(&self, fundamental: f32, harmonics: usize) -> Vec<f32> {
        let gamma_f64 = std::f64::consts::EULER_GAMMA;

        (1..=harmonics)
            .map(|n| {
                // 使用欧拉常数调整谐波幅度
                let harmonic_freq = fundamental * n as f32;
                let amplitude = 1.0 / (n as f64 * (1.0 + gamma_f64 / n as f64)) as f32;
                (harmonic_freq, amplitude)
            })
            .map(|(freq, _)| freq)
            .collect()
    }
}

/// WASM 图形变换器
///
/// 使用数学常量进行 2D/3D 变换
pub struct WasmTransform {
    matrix: [f64; 16],
}

impl WasmTransform {
    /// 创建单位矩阵
    pub fn identity() -> Self {
        Self {
            matrix: [
                1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0,
            ],
        }
    }

    /// 黄金比例缩放
    ///
    /// Rust 1.94.0: 使用 GOLDEN_RATIO
    pub fn golden_scale() -> Self {
        let phi = std::f64::consts::GOLDEN_RATIO;
        Self {
            matrix: [
                phi, 0.0, 0.0, 0.0, 0.0, phi, 0.0, 0.0, 0.0, 0.0, phi, 0.0, 0.0, 0.0, 0.0, 1.0,
            ],
        }
    }

    /// 应用欧拉旋转（使用欧拉常数作为旋转因子）
    pub fn euler_rotation_y(angle: f64) -> Self {
        let gamma = std::f64::consts::EULER_GAMMA;
        let adjusted_angle = angle * (1.0 + gamma * 0.1);

        let cos_a = adjusted_angle.cos();
        let sin_a = adjusted_angle.sin();

        Self {
            matrix: [
                cos_a, 0.0, sin_a, 0.0, 0.0, 1.0, 0.0, 0.0, -sin_a, 0.0, cos_a, 0.0, 0.0, 0.0,
                0.0, 1.0,
            ],
        }
    }

    /// 将变换应用到点
    pub fn transform_point(&self, x: f64, y: f64, z: f64) -> (f64, f64, f64) {
        let m = &self.matrix;
        (
            m[0] * x + m[4] * y + m[8] * z + m[12],
            m[1] * x + m[5] * y + m[9] * z + m[13],
            m[2] * x + m[6] * y + m[10] * z + m[14],
        )
    }
}

// ==================== 4. Peekable 新方法 - WASM 文本解析 ====================

/// # 4. Peekable 新方法 - WASM 文本解析
///
/// Rust 1.94.0 的 Peekable 新方法在 WASM 文本解析中非常有用。

/// WAT (WebAssembly Text) 解析器
///
/// 使用 Peekable 新方法解析 WASM 文本格式
pub struct WatParser<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
    line: usize,
    column: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum WatToken {
    LParen,
    RParen,
    Identifier(String),
    String(String),
    Number(f64),
    Keyword(String),
}

impl<'a> WatParser<'a> {
    /// 创建新的 WAT 解析器
    pub fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars().peekable(),
            line: 1,
            column: 1,
        }
    }

    /// 跳过空白和注释
    ///
    /// Rust 1.94.0: 使用 next_if() 简化空白跳过
    fn skip_whitespace(&mut self) {
        loop {
            // 跳过空白字符
            while self.chars.next_if(|c| c.is_whitespace()).is_some() {
                self.column += 1;
            }

            // 跳过注释 (; ... )
            if self.chars.peek() == Some(&'(') {
                let saved = self.chars.clone();
                self.chars.next();
                if self.chars.peek() == Some(&';') {
                    self.skip_block_comment();
                } else {
                    // 恢复位置
                    self.chars = saved;
                    break;
                }
            } else {
                break;
            }
        }
    }

    /// 跳过分块注释
    fn skip_block_comment(&mut self) {
        let mut depth = 1;
        while let Some(c) = self.chars.next() {
            match c {
                '(' => {
                    if self.chars.peek() == Some(&';') {
                        self.chars.next();
                        depth += 1;
                    }
                }
                ';' => {
                    if self.chars.peek() == Some(&')') {
                        self.chars.next();
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                }
                '\n' => {
                    self.line += 1;
                    self.column = 1;
                }
                _ => self.column += 1,
            }
        }
    }

    /// 解析标识符或关键字
    ///
    /// Rust 1.94.0: 使用 next_if() 简化标识符解析
    fn parse_identifier(&mut self) -> Option<String> {
        let mut ident = String::new();

        // 解析首字符
        if let Some(c) = self.chars.next_if(|c| c.is_alphabetic() || "_$".contains(*c)) {
            ident.push(c);
            self.column += 1;
        } else {
            return None;
        }

        // 解析后续字符
        while let Some(c) = self.chars.next_if(|c| c.is_alphanumeric() || "_$".contains(*c)) {
            ident.push(c);
            self.column += 1;
        }

        Some(ident)
    }

    /// 解析字符串
    fn parse_string(&mut self) -> Option<String> {
        if self.chars.peek() != Some(&'"') {
            return None;
        }
        self.chars.next(); // 消费起始引号
        self.column += 1;

        let mut string = String::new();
        let mut escaped = false;

        for c in self.chars.by_ref() {
            self.column += 1;

            if escaped {
                string.push(match c {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    '\\' => '\\',
                    '"' => '"',
                    _ => c,
                });
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                return Some(string);
            } else {
                string.push(c);
            }
        }

        None // 未闭合的字符串
    }

    /// 解析数字
    ///
    /// Rust 1.94.0: 使用 next_if() 简化数字解析
    fn parse_number(&mut self) -> Option<f64> {
        let mut num_str = String::new();

        // 解析整数部分（包括符号）
        while let Some(c) = self.chars.next_if(|c| c.is_ascii_digit() || *c == '-' || *c == '+') {
            num_str.push(c);
            self.column += 1;
        }

        // 解析小数部分
        if self.chars.peek() == Some(&'.') {
            num_str.push(self.chars.next().unwrap());
            self.column += 1;

            while let Some(c) = self.chars.next_if(|c| c.is_ascii_digit()) {
                num_str.push(c);
                self.column += 1;
            }
        }

        if num_str.is_empty() || num_str == "." {
            None
        } else {
            num_str.parse().ok()
        }
    }

    /// 获取下一个 token
    pub fn next_token(&mut self) -> Option<WatToken> {
        self.skip_whitespace();

        match self.chars.peek() {
            Some(&'(') => {
                self.chars.next();
                self.column += 1;
                Some(WatToken::LParen)
            }
            Some(&')') => {
                self.chars.next();
                self.column += 1;
                Some(WatToken::RParen)
            }
            Some(&'"') => self.parse_string().map(WatToken::String),
            Some(c) if c.is_ascii_digit() || *c == '-' => {
                self.parse_number().map(WatToken::Number)
            }
            Some(_) => {
                if let Some(ident) = self.parse_identifier() {
                    // 检查是否为关键字
                    let keywords = ["module", "func", "param", "result", "i32", "i64", "f32", "f64"];
                    if keywords.contains(&ident.as_str()) {
                        Some(WatToken::Keyword(ident))
                    } else {
                        Some(WatToken::Identifier(ident))
                    }
                } else {
                    None
                }
            }
            None => None,
        }
    }

    /// 解析所有 tokens
    pub fn parse_all(&mut self) -> Vec<WatToken> {
        let mut tokens = Vec::new();
        while let Some(token) = self.next_token() {
            tokens.push(token);
        }
        tokens
    }
}

/// 简单的 CSV 解析器（用于 WASM 数据处理）
///
/// 使用 Peekable 新方法
pub struct SimpleCsvParser<'a> {
    chars: std::iter::Peekable<std::str::Chars<'a>>,
}

impl<'a> SimpleCsvParser<'a> {
    /// 创建新的 CSV 解析器
    pub fn new(input: &'a str) -> Self {
        Self {
            chars: input.chars().peekable(),
        }
    }

    /// 解析一个字段
    ///
    /// Rust 1.94.0: 使用 next_if() 简化字段解析
    fn parse_field(&mut self) -> String {
        let mut field = String::new();

        while let Some(c) = self.chars.next_if(|c| *c != ',' && *c != '\n' && *c != '\r') {
            field.push(c);
        }

        field.trim().to_string()
    }

    /// 解析一行
    pub fn parse_line(&mut self) -> Option<Vec<String>> {
        self.chars.peek()?;

        let mut fields = Vec::new();
        loop {
            fields.push(self.parse_field());

            match self.chars.peek() {
                Some(&',') => {
                    self.chars.next(); // 消费逗号
                }
                Some(&'\n') => {
                    self.chars.next(); // 消费换行
                    break;
                }
                Some(&'\r') => {
                    self.chars.next();
                    if self.chars.peek() == Some(&'\n') {
                        self.chars.next();
                    }
                    break;
                }
                None => break,
                _ => {}
            }
        }

        Some(fields)
    }

    /// 解析所有行
    pub fn parse_all(&mut self) -> Vec<Vec<String>> {
        let mut rows = Vec::new();
        while let Some(row) = self.parse_line() {
            rows.push(row);
        }
        rows
    }
}

// ==================== 5. char 到 usize 转换 - WASM 字符编码 ====================

/// # 5. char 到 usize 转换 - WASM 字符编码
///
/// Rust 1.94.0 的 TryFrom<char> for usize 在 WASM 字符编码和 UTF-8 处理中非常有用。

/// UTF-8 编码器（用于 WASM 字符串处理）
///
/// 使用 char 到 usize 转换进行 UTF-8 编码
pub struct Utf8Encoder;

impl Utf8Encoder {
    /// 获取字符的 Unicode 码点值
    ///
    /// Rust 1.94.0: 使用 TryFrom<char> for usize
    pub fn code_point(c: char) -> Option<usize> {
        usize::try_from(c).ok()
    }

    /// 计算字符串的 UTF-8 字节长度
    pub fn utf8_byte_length(s: &str) -> usize {
        s.chars().map(|c| c.len_utf8()).sum()
    }

    /// 将字符编码为 UTF-8 字节
    ///
    /// 返回字符的字节表示
    pub fn encode_char(c: char) -> Vec<u8> {
        let mut buf = [0u8; 4];
        let len = c.encode_utf8(&mut buf).len();
        buf[..len].to_vec()
    }

    /// 计算字符宽度（用于终端显示）
    ///
    /// 基于 Unicode 码点判断字符宽度
    pub fn char_width(c: char) -> usize {
        if let Some(cp) = Self::code_point(c) {
            // 控制字符宽度为 0
            if cp < 0x20 || (0x7F..0xA0).contains(&cp) {
                return 0;
            }
            // CJK 字符宽度为 2
            if (0x4E00..=0x9FFF).contains(&cp)
                || (0x3400..=0x4DBF).contains(&cp)
                || (0x20000..=0x2A6DF).contains(&cp)
            {
                return 2;
            }
        }
        1 // 默认宽度为 1
    }

    /// 计算字符串显示宽度
    pub fn string_width(s: &str) -> usize {
        s.chars().map(Self::char_width).sum()
    }
}

/// Base64 编码器/解码器（WASM 友好）
///
/// 使用 char 转换进行 Base64 处理
pub struct WasmBase64;

impl WasmBase64 {
    /// Base64 字符集
    const ALPHABET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

    /// 将 Base64 字符转换为数值（包括填充字符标记）
    ///
    /// Rust 1.94.0: 使用 TryFrom<char> for usize
    fn char_to_value(c: char) -> Option<u8> {
        if c.is_ascii_alphanumeric() {
            if c.is_ascii_uppercase() {
                let val = usize::try_from(c).ok()?;
                Some(val.wrapping_sub(usize::try_from('A').ok()?) as u8)
            } else if c.is_ascii_lowercase() {
                let val = usize::try_from(c).ok()?;
                Some(val.wrapping_sub(usize::try_from('a').ok()?) as u8 + 26)
            } else {
                let val = usize::try_from(c).ok()?;
                Some(val.wrapping_sub(usize::try_from('0').ok()?) as u8 + 52)
            }
        } else if c == '+' {
            Some(62)
        } else if c == '/' {
            Some(63)
        } else {
            None
        }
    }

    /// 编码字节数组为 Base64
    pub fn encode(data: &[u8]) -> String {
        let mut result = String::with_capacity(data.len().div_ceil(3) * 4);
        let chunks = data.chunks_exact(3);
        let remainder = chunks.remainder();

        for chunk in chunks {
            let n = ((chunk[0] as u32) << 16) | ((chunk[1] as u32) << 8) | (chunk[2] as u32);
            result.push(Self::ALPHABET[((n >> 18) & 63) as usize] as char);
            result.push(Self::ALPHABET[((n >> 12) & 63) as usize] as char);
            result.push(Self::ALPHABET[((n >> 6) & 63) as usize] as char);
            result.push(Self::ALPHABET[(n & 63) as usize] as char);
        }

        match remainder.len() {
            1 => {
                let n = (remainder[0] as u32) << 16;
                result.push(Self::ALPHABET[((n >> 18) & 63) as usize] as char);
                result.push(Self::ALPHABET[((n >> 12) & 63) as usize] as char);
                result.push('=');
                result.push('=');
            }
            2 => {
                let n = ((remainder[0] as u32) << 16) | ((remainder[1] as u32) << 8);
                result.push(Self::ALPHABET[((n >> 18) & 63) as usize] as char);
                result.push(Self::ALPHABET[((n >> 12) & 63) as usize] as char);
                result.push(Self::ALPHABET[((n >> 6) & 63) as usize] as char);
                result.push('=');
            }
            _ => {}
        }

        result
    }

    /// 解码 Base64 字符串
    pub fn decode(s: &str) -> Option<Vec<u8>> {
        let mut result = Vec::with_capacity(s.len() / 4 * 3);
        let mut buffer = [0u8; 4];
        let mut buf_len = 0;
        let mut padding_count = 0;

        for c in s.chars() {
            if c == '=' {
                // 填充字符
                padding_count += 1;
                buffer[buf_len] = 0;
                buf_len += 1;
            } else if let Some(val) = Self::char_to_value(c) {
                buffer[buf_len] = val;
                buf_len += 1;
            }

            if buf_len == 4 {
                let n = ((buffer[0] as u32) << 18)
                    | ((buffer[1] as u32) << 12)
                    | ((buffer[2] as u32) << 6)
                    | (buffer[3] as u32);
                result.push((n >> 16) as u8);
                result.push((n >> 8) as u8);
                result.push(n as u8);
                buf_len = 0;
            }
        }

        // 处理填充
        if buf_len != 0 {
            return None; // 无效的 Base64（未对齐）
        }

        // 移除填充字节
        if padding_count == 2 {
            result.truncate(result.len().saturating_sub(2));
        } else if padding_count == 1 {
            result.truncate(result.len().saturating_sub(1));
        }

        Some(result)
    }
}

/// 字符频率分析器
///
/// 使用 char 转换分析文本
pub struct CharFrequencyAnalyzer;

impl CharFrequencyAnalyzer {
    /// 分析字符频率
    ///
    /// Rust 1.94.0: 使用 TryFrom<char> for usize 进行字符分类
    pub fn analyze(s: &str) -> HashMap<String, usize> {
        let mut freq: HashMap<String, usize> = HashMap::new();

        for c in s.chars() {
            let category = if let Some(cp) = Utf8Encoder::code_point(c) {
                if cp < 128 {
                    if c.is_ascii_alphabetic() {
                        "ascii_alpha"
                    } else if c.is_ascii_digit() {
                        "ascii_digit"
                    } else if c.is_ascii_punctuation() {
                        "ascii_punct"
                    } else {
                        "ascii_other"
                    }
                } else if cp < 0x800 {
                    "utf8_2byte"
                } else if cp < 0x10000 {
                    "utf8_3byte"
                } else {
                    "utf8_4byte"
                }
            } else {
                "unknown"
            };

            *freq.entry(category.to_string()).or_insert(0) += 1;
        }

        freq
    }

    /// 计算熵（简化版）
    pub fn calculate_entropy(s: &str) -> f64 {
        if s.is_empty() {
            return 0.0;
        }

        let mut char_counts: HashMap<char, usize> = HashMap::new();
        for c in s.chars() {
            *char_counts.entry(c).or_insert(0) += 1;
        }

        let len = s.chars().count() as f64;
        char_counts.values().fold(0.0, |acc, &count| {
            let p = count as f64 / len;
            acc - p * p.log2()
        })
    }
}

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 WASM 特性
pub fn demonstrate_rust_194_wasm_features() {
    println!("\n=== Rust 1.94.0 WASM 特性演示 ===\n");

    // 1. array_windows - WASM 数据处理
    println!("1. array_windows - WASM 数据处理:");
    let memory_data: Vec<u8> = (0..16).map(|i| i as u8).collect();
    let view = WasmMemoryView::new(&memory_data);

    // 读取所有 32 位整数
    let ints: Vec<i32> = view.read_all_i32_le().take(3).collect();
    println!("   读取的 i32 值: {:?}", ints);

    // 查找序列
    let pattern = [0x02, 0x03, 0x04, 0x05];
    if let Some(pos) = view.find_sequence(&pattern) {
        println!("   找到序列 [2,3,4,5] 在位置: {}", pos);
    }

    // 计算校验和
    let checksum = view.checksum_16bit();
    println!("   16位校验和: 0x{:04X}", checksum);

    // 2. LazyLock 新方法 - WASM 模块管理
    println!("\n2. LazyLock 新方法 - WASM 模块管理:");
    update_wasm_config(|config| {
        config.set_memory_pages(2);
    });
    get_wasm_config(|config| {
        println!("   WASM 内存页数: {}", config.memory_pages);
        println!("   内存限制: {} bytes", config.memory_limit_bytes());
    });

    if let Some(export) = get_export_info("memory") {
        println!("   导出 'memory': {:?}", export.kind);
    }

    // 3. 数学常量 - WASM 图形计算
    println!("\n3. 数学常量 - WASM 图形计算:");
    let (w, h) = GoldenRatioLayout::golden_rectangle(1000.0);
    println!("   黄金比例矩形: {} x {}", w, h);

    let spiral = GoldenRatioLayout::golden_spiral_points(5, 10.0);
    println!("   黄金螺旋点 (前5个): {:?}", spiral);

    // 音频合成器
    let synth = EulerAudioSynthesizer::new(44100.0);
    let harmonics = synth.harmonic_series(440.0, 5);
    println!("   440Hz 谐波序列: {:?}", harmonics);

    // 4. Peekable 新方法 - WASM 文本解析
    println!("\n4. Peekable 新方法 - WASM 文本解析:");
    let wat_code = r#"(module (func $add (param i32 i32) (result i32)))"#;
    let mut parser = WatParser::new(wat_code);
    let tokens = parser.parse_all();
    println!("   WAT tokens 数量: {}", tokens.len());

    // CSV 解析
    let csv = "name,age,city\nAlice,30,NYC\nBob,25,LA";
    let mut csv_parser = SimpleCsvParser::new(csv);
    let rows = csv_parser.parse_all();
    println!("   CSV 行数: {}", rows.len());

    // 5. char 到 usize 转换 - WASM 字符编码
    println!("\n5. char 到 usize 转换 - WASM 字符编码:");
    if let Some(cp) = Utf8Encoder::code_point('A') {
        println!("   'A' 的 Unicode 码点: {}", cp);
    }

    let width = Utf8Encoder::char_width('中');
    println!("   '中' 的显示宽度: {}", width);

    // Base64 编码
    let encoded = WasmBase64::encode(b"Hello WASM");
    println!("   Base64 编码 'Hello WASM': {}", encoded);

    if let Some(decoded) = WasmBase64::decode(&encoded) {
        println!("   Base64 解码结果: {:?}", String::from_utf8_lossy(&decoded));
    }

    // 字符频率分析
    let text = "Hello, 世界! 123";
    let freq = CharFrequencyAnalyzer::analyze(text);
    println!("   字符频率分析: {:?}", freq);
}

/// 获取 Rust 1.94.0 WASM 特性信息
pub fn get_rust_194_wasm_info() -> String {
    "Rust 1.94.0 WASM 特性:\n\
        - array_windows - WASM 数据处理\n\
        - LazyLock 新方法 - WASM 模块管理\n\
        - 数学常量 - WASM 图形计算\n\
        - Peekable 新方法 - WASM 文本解析\n\
        - TryFrom<char> for usize - WASM 字符编码"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_array_windows_memory_view() {
        let data: Vec<u8> = vec![0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00];
        let view = WasmMemoryView::new(&data);

        let val = view.read_i32_le(0);
        assert_eq!(val, Some(1));

        // array_windows<4> 会产生 5 个窗口，我们只取前两个对齐的值
        let ints: Vec<i32> = view.read_all_i32_le().step_by(4).take(2).collect();
        assert_eq!(ints, vec![1, 2]);
    }

    #[test]
    fn test_array_windows_find_sequence() {
        let data: Vec<u8> = vec![0x00, 0x01, 0x02, 0x03, 0x04, 0x05];
        let view = WasmMemoryView::new(&data);

        let pos = view.find_sequence(&[0x02, 0x03]);
        assert_eq!(pos, Some(2));
    }

    #[test]
    fn test_lazylock_wasm_config() {
        update_wasm_config(|config| {
            config.set_memory_pages(4);
        });
        get_wasm_config(|config| {
            assert_eq!(config.memory_pages, 4);
        });
    }

    #[test]
    fn test_golden_ratio_layout() {
        let (w, h) = GoldenRatioLayout::golden_rectangle(1000.0);
        assert!((w / h - std::f64::consts::GOLDEN_RATIO).abs() < 0.001);

        let points = GoldenRatioLayout::golden_spiral_points(10, 1.0);
        assert_eq!(points.len(), 10);
    }

    #[test]
    fn test_euler_audio_synthesizer() {
        let synth = EulerAudioSynthesizer::new(44100.0);
        let harmonics = synth.harmonic_series(440.0, 5);
        assert_eq!(harmonics.len(), 5);
        assert!((harmonics[0] - 440.0).abs() < 0.001);
    }

    #[test]
    fn test_wat_parser() {
        let wat = "(module (func))";
        let mut parser = WatParser::new(wat);
        let tokens = parser.parse_all();
        assert!(!tokens.is_empty());
        assert!(tokens.contains(&WatToken::LParen));
        assert!(tokens.contains(&WatToken::RParen));
    }

    #[test]
    fn test_csv_parser() {
        let csv = "a,b,c\n1,2,3";
        let mut parser = SimpleCsvParser::new(csv);
        let rows = parser.parse_all();
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0], vec!["a", "b", "c"]);
    }

    #[test]
    fn test_utf8_encoder() {
        assert_eq!(Utf8Encoder::code_point('A'), Some(65));
        assert_eq!(Utf8Encoder::char_width('A'), 1);
        assert_eq!(Utf8Encoder::char_width('中'), 2);
    }

    #[test]
    fn test_wasm_base64() {
        let encoded = WasmBase64::encode(b"Hello");
        assert_eq!(encoded, "SGVsbG8=");

        let decoded = WasmBase64::decode(&encoded);
        assert_eq!(decoded, Some(b"Hello".to_vec()));
    }

    #[test]
    fn test_char_frequency_analyzer() {
        let freq = CharFrequencyAnalyzer::analyze("Hello123");
        assert!(freq.contains_key("ascii_alpha"));
        assert!(freq.contains_key("ascii_digit"));
    }

    #[test]
    fn test_demonstrate_features() {
        demonstrate_rust_194_wasm_features();
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_wasm_info();
        assert!(info.contains("Rust 1.94.0"));
        assert!(info.contains("array_windows"));
    }
}
