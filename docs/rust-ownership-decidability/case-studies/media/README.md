# 音视频处理开发指南

> Rust在多媒体处理领域的高性能应用

---

## 目录

- [音视频处理开发指南](#音视频处理开发指南)
  - [目录](#目录)
  - [1. 音视频处理概述](#1-音视频处理概述)
    - [1.1 为什么Rust适合音视频处理](#11-为什么rust适合音视频处理)
    - [1.2 主要库和框架](#12-主要库和框架)
  - [2. 音频处理](#2-音频处理)
    - [2.1 音频播放](#21-音频播放)
    - [2.2 音频解码（Symphonia）](#22-音频解码symphonia)
    - [2.3 数字信号处理](#23-数字信号处理)
  - [3. 视频编解码](#3-视频编解码)
    - [3.1 使用FFmpeg](#31-使用ffmpeg)
  - [4. 流媒体](#4-流媒体)
    - [4.1 RTMP服务器](#41-rtmp服务器)
    - [4.2 WebRTC](#42-webrtc)
  - [5. 实时通信](#5-实时通信)
    - [5.1 低延迟音频采集](#51-低延迟音频采集)
  - [6. 完整示例：媒体播放器](#6-完整示例媒体播放器)
  - [7. 性能优化](#7-性能优化)
    - [7.1 SIMD加速](#71-simd加速)
    - [7.2 零拷贝处理](#72-零拷贝处理)
  - [总结](#总结)

---

## 1. 音视频处理概述

### 1.1 为什么Rust适合音视频处理

| 特性 | 优势 | 应用场景 |
|------|------|----------|
| **内存安全** | 无缓冲区溢出 | 编解码器安全 |
| **零成本抽象** | 高性能处理 | 实时流 |
| **并发安全** | 无数据竞争 | 并行编解码 |
| **确定性** | 无GC停顿 | 实时系统 |

### 1.2 主要库和框架

**音频处理**:

- `rodio` - 播放库
- `symphonia` - 纯Rust音频解码
- `fundsp` - 数字信号处理
- `rubato` - 采样率转换

**视频处理**:

- `ffmpeg-next` - FFmpeg绑定
- `gstreamer` - 多媒体框架
- `rav1e` - AV1编码器

**流媒体**:

- `webrtc` - WebRTC实现
- `rtmp` - RTMP协议

---

## 2. 音频处理

### 2.1 音频播放

```rust
use rodio::{Decoder, OutputStream, Sink};
use std::fs::File;
use std::io::BufReader;

fn play_audio(path: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 获取默认输出设备
    let (_stream, stream_handle) = OutputStream::try_default()?;
    let sink = Sink::try_new(&stream_handle)?;

    // 加载音频文件
    let file = BufReader::new(File::open(path)?);
    let source = Decoder::new(file)?;

    // 播放
    sink.append(source);
    sink.sleep_until_end();

    Ok(())
}
```

### 2.2 音频解码（Symphonia）

```rust
use symphonia::core::audio::{AudioBufferRef, SampleBuffer};
use symphonia::core::codecs::{DecoderOptions, CODEC_TYPE_NULL};
use symphonia::core::formats::FormatOptions;
use symphonia::core::io::MediaSourceStream;
use symphonia::core::meta::MetadataOptions;
use symphonia::core::probe::Hint;

fn decode_audio(path: &str) -> Result<Vec<f32>, Box<dyn std::error::Error>> {
    // 打开文件
    let file = std::fs::File::open(path)?;
    let mss = MediaSourceStream::new(Box::new(file), Default::default());

    // 探测格式
    let hint = Hint::new();
    let meta_opts: MetadataOptions = Default::default();
    let fmt_opts: FormatOptions = Default::default();

    let probed = symphonia::default::get_probe()
        .format(&hint, mss, &fmt_opts, &meta_opts)?;

    let mut format = probed.format;

    // 找到默认音频轨道
    let track = format.tracks()
        .iter()
        .find(|t| t.codec_params.codec != CODEC_TYPE_NULL)
        .ok_or("No audio track")?;

    // 创建解码器
    let dec_opts: DecoderOptions = Default::default();
    let mut decoder = symphonia::default::get_codecs()
        .make(&track.codec_params, &dec_opts)?;

    // 解码循环
    let mut sample_buffer: Option<SampleBuffer<f32>> = None;
    let mut samples = Vec::new();

    loop {
        let packet = match format.next_packet()? {
            Ok(packet) => packet,
            Err(_) => break,
        };

        // 解码
        match decoder.decode(&packet)? {
            Ok(decoded) => {
                if sample_buffer.is_none() {
                    let spec = *decoded.spec();
                    sample_buffer = Some(
                        SampleBuffer::<f32>::new(decoded.capacity() as u64, spec)
                    );
                }

                if let Some(buf) = &mut sample_buffer {
                    buf.copy_interleaved_ref(decoded);
                    samples.extend_from_slice(buf.samples());
                }
            }
            Err(_) => continue,
        }
    }

    Ok(samples)
}
```

### 2.3 数字信号处理

```rust
use fundsp::hacker32::*;

fn create_effect_chain() -> impl AudioUnit32 {
    let cutoff = 1000.0;
    let q = 0.7;

    let filter = lowpass_hz(cutoff, q);
    let reverb = reverb_stereo(10.0, 0.3, 0.5, 0.8, 0.9);

    filter >> reverb
}
```

---

## 3. 视频编解码

### 3.1 使用FFmpeg

```rust
use ffmpeg_next as ffmpeg;
use ffmpeg::format::{input, Pixel};
use ffmpeg::media::Type;
use ffmpeg::software::scaling::{context::Context, flag::Flags};
use ffmpeg::util::frame::video::Video;

fn decode_video(path: &str) -> Result<(), Box<dyn std::error::Error>> {
    ffmpeg::init()?;

    let mut ictx = input(&path)?;
    let input_stream = ictx.streams()
        .best(Type::Video)
        .ok_or("No video stream")?;

    let video_stream_index = input_stream.index();
    let context_decoder =
        ffmpeg::codec::context::Context::from_parameters(input_stream.parameters())?;
    let mut decoder = context_decoder.decoder().video()?;

    let mut scaler = Context::get(
        decoder.format(),
        decoder.width(),
        decoder.height(),
        Pixel::RGB24,
        decoder.width(),
        decoder.height(),
        Flags::BILINEAR,
    )?;

    let mut frame = Video::empty();
    let mut rgb_frame = Video::empty();

    for (stream, packet) in ictx.packets() {
        if stream.index() == video_stream_index {
            decoder.send_packet(&packet)?;

            while decoder.receive_frame(&mut frame).is_ok() {
                scaler.run(&frame, &mut rgb_frame)?;
                let data = rgb_frame.data(0);
            }
        }
    }

    Ok(())
}
```

---

## 4. 流媒体

### 4.1 RTMP服务器

```rust
use std::sync::Arc;
use tokio::sync::{mpsc, RwLock};
use std::collections::HashMap;

struct StreamHub {
    streams: Arc<RwLock<HashMap<String, mpsc::Sender<Vec<u8>>>>>,
}

impl StreamHub {
    async fn publish(&self, stream_key: &str, data: Vec<u8>) {
        let streams = self.streams.read().await;
        if let Some(tx) = streams.get(stream_key) {
            let _ = tx.send(data).await;
        }
    }
}
```

### 4.2 WebRTC

```rust
use webrtc::api::APIBuilder;
use webrtc::peer_connection::configuration::RTCConfiguration;
use webrtc::peer_connection::RTCPeerConnection;
use webrtc::ice_transport::ice_server::RTCIceServer;

async fn create_peer_connection() -> Result<Arc<RTCPeerConnection>, Box<dyn std::error::Error>> {
    let config = RTCConfiguration {
        ice_servers: vec![
            RTCIceServer {
                urls: vec!["stun:stun.l.google.com:19302".to_string()],
                ..Default::default()
            }
        ],
        ..Default::default()
    };

    let api = APIBuilder::new().build();
    let pc = Arc::new(api.new_peer_connection(config).await?);

    Ok(pc)
}
```

---

## 5. 实时通信

### 5.1 低延迟音频采集

```rust
use cpal::traits::{DeviceTrait, HostTrait, StreamTrait};
use cpal::SampleFormat;
use std::sync::mpsc;

fn capture_audio() -> Result<mpsc::Receiver<Vec<f32>>, Box<dyn std::error::Error>> {
    let host = cpal::default_host();
    let device = host.default_input_device()
        .ok_or("No input device")?;

    let config = device.default_input_config()?;
    let (tx, rx) = mpsc::channel::<Vec<f32>>();

    let err_fn = |err| eprintln!("Stream error: {}", err);

    let stream = match config.sample_format() {
        SampleFormat::F32 => device.build_input_stream(
            &config.into(),
            move |data: &[f32], _: &_| {
                tx.send(data.to_vec()).unwrap();
            },
            err_fn,
            None,
        )?,
        _ => unimplemented!(),
    };

    stream.play()?;

    Ok(rx)
}
```

---

## 6. 完整示例：媒体播放器

```rust
use std::sync::Arc;
use tokio::sync::mpsc;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum PlayerState {
    Idle,
    Loading,
    Playing,
    Paused,
    Stopped,
    Error,
}

pub struct MediaPlayer {
    state: PlayerState,
    event_sender: mpsc::Sender<PlayerEvent>,
}

#[derive(Debug)]
pub enum PlayerEvent {
    Loading,
    Loaded,
    Playing,
    Paused,
    Stopped,
    EndOfStream,
    Error(String),
}

impl MediaPlayer {
    pub fn new() -> (Self, mpsc::Receiver<PlayerEvent>) {
        let (tx, rx) = mpsc::channel(100);

        let player = Self {
            state: PlayerState::Idle,
            event_sender: tx,
        };

        (player, rx)
    }

    pub async fn load(&mut self, path: &str) -> Result<(), Box<dyn std::error::Error>> {
        self.state = PlayerState::Loading;
        self.emit_event(PlayerEvent::Loading).await;

        // 加载逻辑...

        self.state = PlayerState::Stopped;
        self.emit_event(PlayerEvent::Loaded).await;

        Ok(())
    }

    pub fn play(&mut self) {
        self.state = PlayerState::Playing;
    }

    pub fn pause(&mut self) {
        self.state = PlayerState::Paused;
    }

    async fn emit_event(&self, event: PlayerEvent) {
        let _ = self.event_sender.send(event).await;
    }
}
```

---

## 7. 性能优化

### 7.1 SIMD加速

```rust
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn process_samples_avx2(input: &[f32], output: &mut [f32], gain: f32) {
    let gain_vec = _mm256_set1_ps(gain);

    for i in (0..input.len()).step_by(8) {
        let in_vec = _mm256_loadu_ps(input.as_ptr().add(i));
        let out_vec = _mm256_mul_ps(in_vec, gain_vec);
        _mm256_storeu_ps(output.as_ptr().add(i) as *mut f32, out_vec);
    }
}
```

### 7.2 零拷贝处理

```rust
use std::io::Read;

fn process_large_file_mmap(path: &str) -> Result<(), Box<dyn std::error::Error>> {
    let file = std::fs::File::open(path)?;
    let mmap = unsafe { memmap2::Mmap::map(&file)? };

    process_audio_data(&mmap)?;

    Ok(())
}
```

---

## 总结

Rust在音视频处理领域提供了：

1. **高性能**: 接近C/C++的处理速度
2. **安全性**: 消除缓冲区溢出等漏洞
3. **并发**: 安全的并行编解码
4. **生态**: 丰富的多媒体库

适用场景：媒体服务器、实时通信、编解码器、流媒体等。
