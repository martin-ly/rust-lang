# Flutter + Rust 跨平台开发指南

> **定位**: 使用 `flutter_rust_bridge` 构建高性能跨平台应用
> **适用**: iOS、Android、Desktop、Web
> **版本**: flutter_rust_bridge 2.0+
> **Rust 版本**: 1.96.0+

---

## 📋 目录

- [Flutter + Rust 跨平台开发指南](#flutter--rust-跨平台开发指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🏗️ 项目结构](#️-项目结构)
  - [🔌 基础用法](#-基础用法)
    - [Rust 侧接口定义](#rust-侧接口定义)
    - [Dart 侧调用](#dart-侧调用)
    - [代码生成](#代码生成)
  - [📊 平台支持矩阵](#-平台支持矩阵)
    - [Web 平台限制](#web-平台限制)
  - [🧠 内存安全注意事项](#-内存安全注意事项)
    - [Dart GC vs Rust 所有权](#dart-gc-vs-rust-所有权)
    - [对象生命周期管理](#对象生命周期管理)
    - [线程模型差异](#线程模型差异)
  - [⚡ 性能优化建议](#-性能优化建议)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 概述

`flutter_rust_bridge` (FRB) 是连接 Flutter (Dart) 与 Rust 的高性能桥梁，允许在 Dart 中直接调用 Rust 函数，同时保持 Rust 的内存安全和性能优势。

**核心优势**:

- **零拷贝数据传输**: 二进制数据通过 `Uint8List` 直接共享
- **异步原生支持**: Rust `async` 自动映射为 Dart `Future`
- **Stream 支持**: Rust `Stream` 自动映射为 Dart `Stream`
- **异常传播**: Rust `Result` 自动映射为 Dart `Exception`

```text
架构概览:
┌─────────────┐      Dart FFI      ┌─────────────┐
│  Flutter UI │  ←──────────────→  │  Rust Core  │
│   (Dart)    │   flutter_rust_    │  (业务逻辑)  │
└─────────────┘      bridge         └─────────────┘
       │                                    │
       └──────── 平台通道 (可选) ────────────┘
```

---

## 🏗️ 项目结构

推荐的 FRB 项目目录布局：

```text
my_app/
├── rust/                    # Rust crate
│   ├── src/
│   │   └── api.rs          # 公开的 FFI 接口
│   ├── Cargo.toml
│   └── build.rs
├── lib/
│   └── main.dart           # Flutter 入口
├── ios/
├── android/
├── macos/
├── windows/
├── linux/
└── pubspec.yaml
```

---

## 🔌 基础用法

### Rust 侧接口定义

在 `rust/src/api.rs` 中定义要暴露给 Dart 的函数：

```rust
use flutter_rust_bridge::frb;

/// 同步计算函数
#[frb(sync)]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

/// 异步计算函数
pub async fn fetch_data(url: String) -> Result<String, String> {
    reqwest::get(&url)
        .await
        .map_err(|e| e.to_string())?
        .text()
        .await
        .map_err(|e| e.to_string())
}

/// 返回复杂结构体
#[derive(Debug, Clone)]
pub struct User {
    pub id: u64,
    pub name: String,
    pub email: String,
    pub active: bool,
}

#[frb(sync)]
pub fn get_user(id: u64) -> User {
    User {
        id,
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
        active: true,
    }
}

/// Stream 示例：实时数据流
pub fn counter_stream(max: u32) -> impl Stream<Item = u32> {
    stream::iter(0..max)
}

/// 二进制数据处理（零拷贝场景）
pub fn process_image(data: Vec<u8>) -> Vec<u8> {
    // 图像处理逻辑
    data.into_iter()
        .map(|p| p.saturating_add(10))
        .collect()
}
```

### Dart 侧调用

```dart
import 'package:flutter_rust_bridge/flutter_rust_bridge.dart';
import 'src/rust/api/simple.dart';  // 生成的绑定

class _MyAppState extends State<MyApp> {
  String _result = 'Loading...';

  @override
  void initState() {
    super.initState();
    _callRust();
  }

  Future<void> _callRust() async {
    // 同步调用
    final sum = add(a: 1, b: 2);

    // 异步调用
    final data = await fetchData(url: 'https://api.example.com');

    // 结构体操作
    final user = getUser(id: 42);
    print('User: ${user.name}, ${user.email}');

    // Stream 监听
    await for (final count in counterStream(max: 10)) {
      setState(() => _result = 'Count: $count');
    }

    // 二进制数据
    final processed = await processImage(data: Uint8List.fromList([1, 2, 3]));
  }
}
```

### 代码生成

```bash
# 安装 flutter_rust_bridge_codegen
cargo install flutter_rust_bridge_codegen

# 生成 Dart 绑定
flutter_rust_bridge_codegen generate \
    --rust-input rust/src/api.rs \
    --dart-output lib/src/rust/api/simple.dart \
    --wasm-enabled  # 如果需要 Web 支持
```

---

## 📊 平台支持矩阵

| 平台 | 目标架构 | 支持状态 | 构建命令 | 注意事项 |
|------|----------|----------|----------|----------|
| **iOS** | `aarch64-apple-ios` | ✅ 稳定 | `flutter build ios` | 需配置 Xcode 签名 |
| **iOS Simulator** | `aarch64-apple-ios-sim` | ✅ 稳定 | `flutter build ios --simulator` | Apple Silicon 原生 |
| **Android** | `aarch64-linux-android` | ✅ 稳定 | `flutter build apk` | 需 NDK r23+ |
| **Android (x86_64)** | `x86_64-linux-android` | ✅ 稳定 | `flutter build apk` | 模拟器使用 |
| **macOS** | `aarch64-apple-darwin` | ✅ 稳定 | `flutter build macos` | Apple Silicon |
| **macOS (Intel)** | `x86_64-apple-darwin` | ✅ 稳定 | `flutter build macos` | 通用二进制需 lipo |
| **Windows** | `x86_64-pc-windows-msvc` | ✅ 稳定 | `flutter build windows` | Visual Studio 2019+ |
| **Linux** | `x86_64-unknown-linux-gnu` | ✅ 稳定 | `flutter build linux` | 需 clang/llvm |
| **Web** | `wasm32-unknown-unknown` | ⚠️ 实验 | `flutter build web` | 功能受限，见下方 |

### Web 平台限制

Web 平台通过 WASM 编译 Rust 代码，存在以下限制：

| 特性 | 原生平台 | Web (WASM) |
|------|----------|------------|
| 多线程 | ✅ | ⚠️ 需 COOP/COEP |
| 文件系统 | ✅ | ❌ 需 IndexedDB 模拟 |
| 网络请求 | ✅ | ✅ (Fetch API) |
| 共享内存 | ✅ | ⚠️ SharedArrayBuffer |
| 启动时间 | ~10ms | ~100ms (WASM 加载) |

```yaml
# pubspec.yaml — 启用 Web 支持
dependencies:
  flutter_rust_bridge: ^2.0.0

flutter_rust_bridge:
  wasm: true
```

---

## 🧠 内存安全注意事项

### Dart GC vs Rust 所有权

Dart 使用**标记-清除 GC**，Rust 使用**编译期所有权**。FRB 在边界处自动处理内存转换，但开发者仍需理解以下风险：

```text
内存模型对比:
┌─────────────┐                    ┌─────────────┐
│   Dart GC   │  ←── 桥接层 ───→   │ Rust 所有权  │
│  自动回收   │    自动管理生命周期   │ 确定性释放   │
└─────────────┘                    └─────────────┘
       │                                  │
       ▼                                  ▼
  对象可达性                          Drop trait
  决定生命周期                         精确控制
```

### 对象生命周期管理

```rust
// ⚠️ 危险：返回裸指针或原始引用给 Dart
#[frb]
pub fn get_internal_ref() -> &'static mut Vec<u8> {
    static mut BUFFER: Vec<u8> = Vec::new();
    unsafe { &mut BUFFER }  // 不安全！Dart GC 无法感知
}

// ✅ 正确：使用 Arc 或返回所有权
use std::sync::Arc;

#[frb]
pub fn create_buffer() -> Arc<Vec<u8>> {
    Arc::new(vec![0u8; 1024])
}

// ✅ 正确：Dart 拥有所有权，Rust 侧不保留引用
#[frb]
pub fn transform_data(input: Vec<u8>) -> Vec<u8> {
    input.into_iter().map(|b| b.wrapping_add(1)).collect()
}
```

**关键原则**：

| 原则 | 说明 |
|------|------|
| 所有权转移优先 | 数据跨边界时优先转移所有权，而非共享引用 |
| 避免静态可变状态 | `static mut` 在并发 Dart 调用中会导致 UB |
| 显式释放资源 | 对文件句柄、网络连接等，提供显式 `dispose` 函数 |
| 注意线程亲和性 | Rust `!Send` 类型不可跨 Dart isolate 传递 |

### 线程模型差异

```rust
use flutter_rust_bridge::frb;

// ✅ 安全：Rust 异步在 Tokio 运行时执行，结果通过端口返回 Dart
pub async fn heavy_computation(input: Vec<f64>) -> Vec<f64> {
    tokio::task::spawn_blocking(move || {
        input.into_iter().map(|x| x.sqrt()).collect()
    }).await.unwrap()
}

// ⚠️ 注意：Dart UI isolate 与 Rust 线程池通信有开销
// 对于 < 1ms 的计算，直接在 Dart 中执行可能更快
```

---

## ⚡ 性能优化建议

| 优化点 | 策略 | 预期收益 |
|--------|------|----------|
| 批量传输 | 将多次小调用合并为一次批量调用 | -80% FFI 开销 |
| 零拷贝二进制 | 使用 `Vec<u8>` / `Uint8List` | -100% 拷贝开销 |
| 缓存 Rust 对象 | 使用 `Arc<Mutex<T>>` 全局缓存 | -50% 重复初始化 |
| 避免同步阻塞 | 长计算使用 `async` + `spawn_blocking` | UI 不卡顿 |
| 延迟加载 Rust | `RustLib.init()` 在首屏后调用 | -30% 启动时间 |

```dart
// ✅ 批量调用优于多次单次调用
final results = await Future.wait([
  for (var i = 0; i < 100; i++)
    processItem(id: i),  // 合并为单个 Rust 调用更佳
]);

// ✅ 在 Rust 侧完成聚合
final summary = await processBatch(ids: List.generate(100, (i) => i));
```

---

## 🔗 参考资源

- [flutter_rust_bridge 官方文档](https://cjycode.com/flutter_rust_bridge/)
- [flutter_rust_bridge GitHub](https://github.com/fzyzcjy/flutter_rust_bridge)
- [Dart FFI 指南](https://dart.dev/guides/libraries/c-interop)
- [Rust 交叉编译指南](https://rust-lang.github.io/rustup/cross-compilation.html)
- [项目 crate: c12_wasm](../../crates/c12_wasm/) — WASM 相关示例

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
