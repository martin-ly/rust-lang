# 现代Rust库形式化分析索引

> **范围**: 著名现代开源库的深度形式化分析
> **总库数**: 23+
> **状态**: 持续推进中

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

## 应用级库 (8个) 🆕 新增

| 库名 | 领域 | 关键形式化 | 状态 |
| :--- | :--- | :--- | :--- |
| [axum](./axum-formal-analysis.md) | Web框架 | 类型安全路由、提取器模式 | ✅ |
| [sea-orm](./sea-orm-formal-analysis.md) | 数据库ORM | 类型安全查询、关系映射 | ✅ |
| [clap](./clap-formal-analysis.md) | CLI解析 | 派生宏、类型安全参数 | ✅ |
| [serde](./serde-formal-analysis.md) | 序列化 | 数据模型、零拷贝 | ✅ |
| [tokio](./tokio-runtime-formal-analysis.md) | 异步运行时 | 任务调度、IO驱动 | ✅ |
| [rayon](./rayon-formal-analysis.md) | 并行计算 | 工作窃取、确定性 | ✅ |
| [wasm-bindgen](./wasm-bindgen-formal-analysis.md) | WASM互操作 | FFI边界、内存管理 | ✅ |
| [pyo3](./pyo3-formal-analysis.md) | Python绑定 | GIL管理、类型转换 | ✅ |

---

## 覆盖统计

```
总库数: 23个
- 嵌入式库: 15个 [██████████] 100%
- 应用级库: 8个  [████░░░░░░] 持续推进中

现代特性覆盖:
- GATs (Generic Associated Types): ✅
- RPITIT (Return Position Impl Trait In Trait): ✅
- 异步trait: ✅
- const generics: ✅
- TAIT (Type Alias Impl Trait): ✅
```

---

## 计划扩展

以下著名库计划添加形式化分析：

| 库名 | 领域 | 优先级 |
| :--- | :--- | :--- |
| diesel | ORM | 高 |
| sqlx | 数据库 | 高 |
| actix-web | Web框架 | 中 |
| tonic | gRPC | 中 |
| tracing | 日志 | 中 |
| criterion | 基准测试 | 低 |
| mockall | 测试 | 低 |
| chrono | 时间处理 | 低 |

---

**维护者**: Rust Formal Methods Team
**更新日期**: 2026-03-05
**状态**: 🔄 持续推进中
