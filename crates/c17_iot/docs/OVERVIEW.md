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

### 设备生命周期管理与大规模部署（补全）

- 生命周期阶段
  - 生产与入库：烧录只读设备 ID、初始证书/密钥、信任根
  - 交付与开箱：一次性激活口令/二维码，限制有效期与重放
  - 入网与登记：零接触（ZTP/Just-In-Time Provisioning），绑定租户/项目
  - 运行与维护：证书轮换、策略下发、遥测监控、告警与远程诊断
  - 退役与回收：安全擦除、证书吊销、资产与审计闭环

- 大规模部署实践
  - 分批灰度与金丝雀：波次/分区/设备画像选择；失败自动回滚
  - OTA 策略：差分包、签名与完整性校验、断点续传与失败重试
  - 设备孪生：期望态/报告态对账，幂等重试与冲突解决
  - 凭据管理：短生命周期令牌、mTLS、硬件安全模块（TPM/SE）
  - 观测与压测：端到端时延、吞吐、丢包/抖动容忍度基线

- 清单与门禁
  - 设备唯一性与可追溯：序列号/证书指纹/硬件熵源校验
  - 策略一致性：ACL/Topic 命名/租户隔离；消息大小与频次限额
  - 合规与隐私：数据驻留、最小采集原则、敏感字段脱敏

- 互链
  - 与 `c20_distributed`：边云一致性、离线缓存与冲突合并策略
  - 与 `c12_middlewares`：MQTT/Kafka 网关与可观测性探针复用
