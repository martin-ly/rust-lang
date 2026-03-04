# 现代Rust库形式化分析索引

> **范围**: 著名现代开源库的深度形式化分析
> **总库数**: 39个
> **状态**: ✅ 100% 核心库覆盖完成

---

## 嵌入式库 (15个) ✅ 100%

| 库名 | 领域 | 关键形式化 | 状态 |
| :--- | :--- | :--- | :--- |
| [embassy](./embassy-formal-analysis.md) | 异步运行时 | 静态任务分配、单线程执行器 | ✅ |
| [rtic](./rtic-formal-analysis.md) | 实时调度 | 资源声明、优先级调度 | ✅ |
| [smoltcp](./smoltcp-formal-analysis.md) | TCP/IP栈 | 零拷贝、套接字状态机 | ✅ |
| [embedded-storage](./embedded-storage-formal-analysis.md) | 存储抽象 | 擦除/编程语义 | ✅ |
| [usb-device](./usb-device-formal-analysis.md) | USB设备 | 枚举状态机 | ✅ |
| [littlefs2](./littlefs2-formal-analysis.md) | 文件系统 | 磨损均衡、断电安全 | ✅ |
| [nrf-hal](./nrf-hal-formal-analysis.md) | Nordic HAL | 外设所有权 | ✅ |
| [stm32f4xx-hal](./stm32f4xx-hal-formal-analysis.md) | STM32 HAL | 时钟配置安全 | ✅ |
| [embedded-graphics](./embedded-graphics-formal-analysis.md) | 图形库 | DrawTarget trait | ✅ |
| [panic-probe](./panic-probe-formal-analysis.md) | 调试 | 恐慌捕获 | ✅ |
| [alloc-cortex-m](./alloc-cortex-m-formal-analysis.md) | 内存分配 | 堆分配器 | ✅ |
| [defmt](./defmt-formal-analysis.md) | 日志框架 | 延迟格式化 | ✅ |
| [cortex-m-rt](./cortex-m-rt-formal-analysis.md) | 运行时 | 启动顺序 | ✅ |
| [embedded-hal](./embedded-hal-formal-analysis.md) | 硬件抽象 | 数字/模拟IO trait | ✅ |
| [probe-rs](./probe-rs-formal-analysis.md) | 调试工具 | 调试协议 | ✅ |

---

## 应用级库 (24个) ✅ 100% 核心覆盖

### Web/网络 (7个)

| 库名 | 领域 | 关键形式化 | 状态 |
| :--- | :--- | :--- | :--- |
| [axum](./axum-formal-analysis.md) | Web框架 | 类型安全路由、提取器模式 | ✅ |
| [actix-web](./actix-web-formal-analysis.md) | Actor Web框架 | Actor模型、状态管理 | ✅ |
| [tokio](./tokio-runtime-formal-analysis.md) | 异步运行时 | 任务调度、IO驱动 | ✅ |
| [tonic](./tonic-formal-analysis.md) | gRPC框架 | 流处理、协议升级 | ✅ |
| [reqwest](./reqwest-formal-analysis.md) | HTTP客户端 | 连接池、中间件 | ✅ |
| [hyper](./hyper-formal-analysis.md) | HTTP实现 | 服务trait、流抽象 | ✅ |
| [tower](./tower-formal-analysis.md) | 服务抽象 | 组合子、背压 | ✅ |

### 数据库 (3个)

| 库名 | 领域 | 关键形式化 | 状态 |
| :--- | :--- | :--- | :--- |
| [sea-orm](./sea-orm-formal-analysis.md) | ORM | 类型安全查询、关系映射 | ✅ |
| [diesel](./diesel-formal-analysis.md) | 编译时SQL ORM | 编译时验证、查询DSL | ✅ |
| [sqlx](./sqlx-formal-analysis.md) | 查询宏 | 编译时SQL检查、类型映射 | ✅ |

### 序列化/CLI (2个)

| 库名 | 领域 | 关键形式化 | 状态 |
| :--- | :--- | :--- | :--- |
| [serde](./serde-formal-analysis.md) | 序列化 | 数据模型、零拷贝 | ✅ |
| [clap](./clap-formal-analysis.md) | CLI解析 | 派生宏、类型安全参数 | ✅ |

### 错误处理/日志 (2个)

| 库名 | 领域 | 关键形式化 | 状态 |
| :--- | :--- | :--- | :--- |
| [thiserror/anyhow](./thiserror-anyhow-formal-analysis.md) | 错误处理 | 错误派生、上下文传播 | ✅ |
| [tracing](./tracing-formal-analysis.md) | 分布式跟踪 | Span树、上下文传播 | ✅ |

### 异步基础设施 (3个)

| 库名 | 领域 | 关键形式化 | 状态 |
| :--- | :--- | :--- | :--- |
| [async-trait](./async-trait-formal-analysis.md) | 异步trait | 宏转换、Send边界 | ✅ |
| [tokio-stream](./tokio-stream-formal-analysis.md) | 流处理 | Stream trait、背压 | ✅ |
| [pin-project](./pin-project-formal-analysis.md) | 自引用 | Pin投影、Drop安全 | ✅ |

### 并发原语 (4个)

| 库名 | 领域 | 关键形式化 | 状态 |
| :--- | :--- | :--- | :--- |
| [rayon](./rayon-formal-analysis.md) | 并行计算 | 工作窃取、确定性 | ✅ |
| [crossbeam](./crossbeam-formal-analysis.md) | 无锁结构 | epoch管理、ABA安全 | ✅ |
| [dashmap](./dashmap-formal-analysis.md) | 并发Map | 分片锁、迭代安全 | ✅ |
| [parking_lot](./parking_lot-formal-analysis.md) | 同步原语 | 紧凑锁、无中毒 | ✅ |

### FFI/工具 (3个)

| 库名 | 领域 | 关键形式化 | 状态 |
| :--- | :--- | :--- | :--- |
| [wasm-bindgen](./wasm-bindgen-formal-analysis.md) | WASM互操作 | FFI边界、内存管理 | ✅ |
| [pyo3](./pyo3-formal-analysis.md) | Python绑定 | GIL管理、类型转换 | ✅ |
| [chrono](./chrono-formal-analysis.md) | 时间处理 | 日历系统、时区 | ✅ |
| [bytes](./bytes-formal-analysis.md) | 字节缓冲 | 零拷贝、引用计数 | ✅ |

---

## 覆盖统计

```
总库数: 39个
- 嵌入式库: 15个 [██████████] 100% ✅
- 应用级库: 24个 [██████████] 100% ✅

现代特性覆盖:
- GATs (Generic Associated Types): ✅
- RPITIT (Return Position Impl Trait In Trait): ✅
- 异步trait: ✅
- const generics: ✅
- TAIT (Type Alias Impl Trait): ✅
- Pin/Unpin: ✅
- 过程宏: ✅
- 特殊化: 🔄 跟踪中
```

---

## 形式化内容总计

| 指标 | 数量 |
| :--- | :--- |
| 总库数 | 39个 |
| 总定义数 | 200+ |
| 总定理数 | 120+ |
| 代码示例 | 100+ |

---

**维护者**: Rust Formal Methods Team
**更新日期**: 2026-03-05
**状态**: ✅ 100% 核心库覆盖完成
