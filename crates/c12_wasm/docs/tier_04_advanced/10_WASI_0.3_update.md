# WASI 0.3 更新与前沿追踪

> **文档状态**: 🧪 前沿追踪
> **更新日期**: 2026-06-01
> **对标版本**: WASI 0.3 (2026-02 发布) / WASI 1.0 (预计 2026Q4-2027Q1)
> **难度等级**: ⭐⭐⭐⭐⭐

---

## 一、WASI 演进时间线

```text
WASI 0.1 (Preview 1) ──→ 2022 ──→ 模块级系统调用，基本文件/网络
WASI 0.2 (Preview 2) ──→ 2024 ──→ 组件模型引入，WIT 接口，类型安全
WASI 0.3 (Preview 3) ──→ 2026-02 ──→ 原生异步 I/O，Worlds 升级
WASI 1.0 (Standard)   ──→ 2026Q4~2027Q1 ──→ 标准化，替代部分容器场景
```

---

## 二、WASI 0.3 核心变更

### 2.1 原生异步 I/O（最大变革）

WASI 0.3 引入基于 **WASI-IO** 接口的原生异步能力，组件可通过 `future` 和 `stream` 类型进行异步交互，无需运行时轮询。

**WIT 定义示例**:

```wit
package wasi:io@0.3.0;

interface streams {
    // 异步字节流
    resource input-stream {
        read: func(len: u64) -> future<result<list<u8>, stream-error>>;
        subscribe: func() -> pollable;
    }

    // 异步写入
    resource output-stream {
        write: func(buf: list<u8>) -> future<result<u64, stream-error>>;
        flush: func() -> future<result<(), stream-error>>;
    }
}
```

**与 0.2 的对比**:

| 维度 | WASI 0.2 | WASI 0.3 |
|:---|:---|:---|
| I/O 模型 | 阻塞式 + 外部运行时模拟 | 原生异步 (`future`/`stream`) |
| 组件间通信 | 同步函数调用 | 异步 WIT 接口 |
| 与 Rust async 集成 | 需手动桥接 | 编译器自动生成绑定 |
| 性能 | 上下文切换开销 | 零成本抽象（目标）|

### 2.2 简化 Worlds

WASI 0.3 简化了 `world` 定义，移除冗余接口，统一为 `wasi:cli` 核心 world：

```wit
// WASI 0.3 简化的命令 world
package wasi:cli@0.3.0;

world command {
    import wasi:io/streams@0.3.0;
    import wasi:io/poll@0.3.0;
    import wasi:clocks/monotonic-clock@0.3.0;
    import wasi:filesystem/types@0.3.0;
    import wasi:sockets/tcp@0.3.0;

    export run: func() -> result;
}
```

### 2.3 资源类型增强

- `borrow<T>` 和 `own<T>` 显式区分资源所有权
- 支持资源析构的异步清理

---

## 三、Rust 1.96 的 WASM 链接器变更

Rust 1.96 调整了 Wasm 目标的链接器行为，与 WASI 演进相关：

**变更**: Wasm 目标不再向链接器传递 `--allow-undefined`。

**影响**: 未定义符号现在产生**硬链接错误**而非静默转为 `"env"` 模块导入。

**迁移方案**:

```rust
// 方案 1: 显式声明导入模块
#[link(wasm_import_module = "env")]
extern "C" {
    fn my_external_func();
}

// 方案 2: 使用 RUSTFLAGS 恢复旧行为（不推荐长期）
// RUSTFLAGS="-Clink-arg=--allow-undefined" cargo build --target wasm32-wasip2
```

---

## 四、WASI 1.0 标准化展望

| 里程碑 | 预计时间 | 目标 |
|:---|:---|:---|
| WASI 0.3 稳定 | 2026 H1 | 原生异步 I/O 成熟 |
| WASI 1.0 提案 | 2026 Q3 | W3C 标准化流程启动 |
| WASI 1.0 发布 | 2026 Q4 ~ 2027 Q1 | 正式 Web 标准 |

**WASI 1.0 的愿景**:

- 替代部分容器工作负载（轻量级、冷启动更快）
- 云原生标准运行时接口
- 与 Kubernetes 集成（runwasi 成熟）

---

## 五、Rust 开发者行动建议

| 场景 | 建议 |
|:---|:---|
| 已有 WASI 0.2 项目 | 监控 0.3 工具链成熟度，暂无需迁移 |
| 新启动 WASM 项目 | 优先使用 `wasm32-wasip2` 目标，为 0.3 做准备 |
| 需要原生异步 WASM | 等待 wit-bindgen 0.3 支持，或实验性使用 |
| 云原生部署 | 关注 Wasmtime LTS 频道（2 年安全支持） |

---

**文档版本**: 1.0
**对应版本**: WASI 0.3 (Preview 3) / Rust 1.96.0+
**最后更新**: 2026-06-01
**状态**: 🧪 前沿追踪

> **权威来源**: [WASI Proposal](https://github.com/WebAssembly/WASI), [Wasmtime Blog](https://bytecodealliance.org/articles), [Rust 1.96 Release Notes](https://github.com/rust-lang/rust/issues/156512)
