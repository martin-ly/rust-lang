# 概览：物联网（c17_iot）

本模块聚焦 IoT 通讯协议、设备管理、安全、边缘计算与可观测性，提供端到端样例与工具链。

---

## 目录导航

- 顶层与总结
  - 顶层说明：`README.md`
  - [docs/FINAL_COMPLETION_SUMMARY.md](./FINAL_COMPLETION_SUMMARY.md)
  - [docs/COMPREHENSIVE_ENHANCEMENT_REPORT.md](./COMPREHENSIVE_ENHANCEMENT_REPORT.md)

- 领域与视图
  - 领域：`docs/domain/iot_view01.md` … `iot_view08.md`
  - 视图：`docs/view/rust_iot01.md` … `rust_iot06.md`
  - OTA：`docs/ota01.md`

- 示例与工具
  - `examples/*.rs`（MQTT/CoAP/LwM2M/OPC UA/边缘/遥测）
  - 组合环境：`examples/_compose/`
  - 脚本：`scripts/*`

---

## 快速开始

1) 运行 `examples/mqtt_minimal.rs` 或 `coap_dtls.rs`
2) 启动 `_compose` 环境并观察指标/日志
3) 阅读 `security_enhanced.rs` 与 `observability_enhanced.rs`

---

## 待完善

- 增补设备生命周期管理与大规模部署实践
- 与 `c20_distributed` 的边缘-云协同架构互链
