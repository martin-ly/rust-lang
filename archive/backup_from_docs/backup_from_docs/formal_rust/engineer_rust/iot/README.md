# 物联网（IoT, Internet of Things）

## 1. 定义与软件工程对标

**物联网**指通过网络将各种物理设备连接起来，实现智能感知与控制。软件工程wiki认为，IoT是智能化系统和边缘计算的基础。
**IoT** means connecting various physical devices via networks for smart sensing and control. In software engineering, IoT is the foundation for intelligent systems and edge computing.

## 2. Rust 1.88 最新特性

- **异步trait**：高效处理设备并发数据流。
- **trait对象向上转型**：便于抽象多种设备协议。
- **LazyCell**：线程本地缓存，适合边缘场景。

## 3. 典型惯用法（Idioms）

- 使用async/await处理高并发设备数据
- 结合serde/cbor高效序列化传感器数据
- 利用trait抽象设备驱动与协议

## 4. 代码示例

```rust
trait Device {
    async fn read(&self) -> SensorData;
}
```

## 5. 软件工程概念对照

- **可扩展性（Scalability）**：异步并发支撑大规模设备接入。
- **安全性（Security）**：类型系统和内存安全防止常见IoT漏洞。
- **低功耗（Low Power）**：零成本抽象优化嵌入式性能。

## 6. FAQ

- Q: Rust如何提升IoT系统安全性？
  A: 静态类型、内存安全和最小化运行时，适合嵌入式与安全敏感场景。

---
