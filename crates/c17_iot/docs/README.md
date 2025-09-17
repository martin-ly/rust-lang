# Rust IoT 系统文档中心

## 📋 模块概述

c17_iot 是一个基于 2025 年 IoT 行业标准架构设计的 Rust IoT 解决方案，对标国际著名大学研究成果，提供完整的物联网通信、设备管理、安全、边缘计算与可观测性功能。

## 🚀 核心特性

### 2025 年标准对标特性

- **国际标准支持** - ISO/IEC 30141、IEC 62443、NIST IoT 基线
- **大学研究成果** - MIT 边缘智能、Stanford 隐私保护、Berkeley 分布式系统
- **增强安全框架** - TLS 1.3、DTLS、OSCORE、X.509 证书管理
- **边缘计算增强** - 云边协同、智能调度、资源管理
- **可观测性完善** - OpenTelemetry、Prometheus、智能告警
- **隐私保护** - 零知识证明、差分隐私、安全多方计算

### 通信协议支持

- **MQTT 5.0** - 完整的 MQTT 客户端实现，支持 TLS 加密
- **CoAP** - 轻量级 CoAP 协议实现，支持 DTLS 安全
- **LwM2M** - 轻量级 M2M 协议，支持设备管理
- **OPC UA** - 工业自动化通信协议支持

### 安全框架

- **TLS 1.3** - 最新传输层安全协议
- **DTLS 1.2/1.3** - 数据报传输层安全
- **OSCORE** - 端到端安全通信 (RFC 8613)
- **X.509 证书管理** - 完整的设备证书生命周期管理
- **访问控制** - RBAC 和 ABAC 双重访问控制

### 边缘计算

- **云边协同** - 智能任务分配和调度
- **资源管理** - 动态资源分配和负载均衡
- **数据流管理** - 实时数据处理和路由
- **多加速器支持** - GPU、TPU、FPGA、NPU

### 可观测性

- **指标收集** - 支持多种指标类型和聚合函数
- **分布式追踪** - 完整的链路追踪和上下文传播
- **智能告警** - 基于规则的告警和升级机制
- **可视化** - 多种仪表板和面板类型

## 📚 文档导航

### 顶层与总结

- [项目说明](../README.md) - 项目概述和快速开始指南
- [最终完成总结](./FINAL_COMPLETION_SUMMARY.md) - 项目完成状态和成果总结
- [综合增强报告](./COMPREHENSIVE_ENHANCEMENT_REPORT.md) - 详细的技术增强报告
- [2025 年标准分析](./2025_IOT_STANDARDS_ANALYSIS.md) - 国际标准对标分析

### 领域与视图

- [IoT 领域视图](./domain/iot_view01.md) - 多角度 IoT 技术领域分析
- [Rust IoT 视图](./view/rust_iot01.md) - Rust 在 IoT 中的应用视图
- [OTA 升级](./ota01.md) - 设备固件升级管理

### 示例与工具

- [示例代码](../examples/) - 完整的可运行示例
- [组合环境](../examples/_compose/) - Docker 组合环境
- [脚本工具](../scripts/) - 一键部署脚本

## 🎯 快速开始

### 1. 基础 MQTT 通信

```bash
# 需要本地 MQTT Broker：localhost:1883
cargo run -p c17_iot --example mqtt_minimal
```

### 2. MQTT TLS 安全通信

```bash
# 需要 TLS MQTT Broker：localhost:8883
cargo run -p c17_iot --example mqtt_tls
```

### 3. CoAP DTLS 通信

```bash
cargo run -p c17_iot --example coap_dtls
```

### 4. LwM2M 设备管理

```bash
cargo run -p c17_iot --example lwm2m_minimal
```

### 5. OPC UA 网关

```bash
cargo run -p c17_iot --example opcua_gateway_mock
```

### 6. OTA 升级模拟

```bash
cargo run -p c17_iot --example ota_simulate
```

### 7. 可观测性示例

```bash
# Prometheus 指标导出
cargo run -p c17_iot --example prom_exporter_http

# OpenTelemetry 追踪
cargo run -p c17_iot --example otel_jaeger

# OpenTelemetry 标准输出
cargo run -p c17_iot --example otel_stdout
```

### 8. 数据管道示例

```bash
# Kafka 生产者（需要启用 kafka 特性）
cargo run -p c17_iot --example kafka_producer --features kafka

# InfluxDB 集成（需要启用 influx 特性）
cargo run -p c17_iot --example influxdb_integration --features influx
```

## 🏗️ 项目结构

```text
c17_iot/
├── src/
│   ├── lib.rs                    # 主库文件
│   ├── types.rs                  # 核心类型定义
│   ├── communication/            # 通信协议模块
│   │   ├── mqtt.rs              # MQTT 实现
│   │   ├── coap.rs              # CoAP 实现
│   │   ├── lwm2m.rs             # LwM2M 实现
│   │   └── opcua.rs             # OPC UA 实现
│   ├── security/                 # 安全模块
│   │   ├── tls.rs               # TLS 实现
│   │   ├── dtls.rs              # DTLS 实现
│   │   ├── oscore.rs            # OSCORE 实现
│   │   └── certificates.rs      # 证书管理
│   ├── edge_computing/           # 边缘计算模块
│   │   ├── scheduler.rs         # 任务调度
│   │   ├── resource_manager.rs  # 资源管理
│   │   └── data_flow.rs         # 数据流管理
│   ├── observability/            # 可观测性模块
│   │   ├── metrics.rs           # 指标收集
│   │   ├── tracing.rs           # 分布式追踪
│   │   └── alerting.rs          # 告警系统
│   └── university_research/      # 大学研究成果对标
│       ├── mit_edge.rs          # MIT 边缘智能
│       ├── stanford_privacy.rs  # Stanford 隐私保护
│       └── berkeley_distributed.rs # Berkeley 分布式系统
├── examples/                     # 示例代码
│   ├── mqtt_minimal.rs          # MQTT 基础示例
│   ├── mqtt_tls.rs              # MQTT TLS 示例
│   ├── coap_dtls.rs             # CoAP DTLS 示例
│   ├── lwm2m_minimal.rs         # LwM2M 示例
│   ├── opcua_gateway_mock.rs    # OPC UA 示例
│   ├── ota_simulate.rs          # OTA 升级示例
│   ├── prom_exporter_http.rs    # Prometheus 示例
│   ├── otel_jaeger.rs           # OpenTelemetry 示例
│   ├── kafka_producer.rs        # Kafka 示例
│   └── _compose/                # Docker 组合环境
├── docs/                         # 文档目录
├── scripts/                      # 部署脚本
├── Cargo.toml                    # 项目配置
└── README.md                     # 项目说明
```

## 🧪 测试与基准测试

### 运行测试

```bash
# 运行所有测试
cargo test -p c17_iot

# 运行特定模块测试
cargo test -p c17_iot communication
cargo test -p c17_iot security
cargo test -p c17_iot edge_computing
cargo test -p c17_iot observability
```

### 运行示例

```bash
# 基础通信示例
cargo run -p c17_iot --example mqtt_minimal
cargo run -p c17_iot --example coap_dtls

# 安全通信示例
cargo run -p c17_iot --example mqtt_tls
cargo run -p c17_iot --example mqtt_tls_strict

# 可观测性示例
cargo run -p c17_iot --example prom_exporter_http
cargo run -p c17_iot --example otel_jaeger
```

### 运行基准测试

```bash
cargo bench -p c17_iot
```

## 🔐 安全特性

### 传输层安全

- **TLS 1.3** - 零往返时间握手，提升性能
- **DTLS 1.2/1.3** - 数据报传输层安全
- **证书验证** - 完整的 X.509 证书链验证
- **主机名验证** - 防止中间人攻击

### 应用层安全

- **OSCORE** - 端到端安全通信
- **设备认证** - 基于证书的设备身份验证
- **访问控制** - 细粒度的权限管理
- **审计日志** - 完整的操作审计记录

### 隐私保护

- **零知识证明** - 保护敏感数据隐私
- **差分隐私** - 统计查询隐私保护
- **安全多方计算** - 多方数据协作计算
- **数据脱敏** - 敏感数据自动脱敏

## 🌐 通信协议

### MQTT 5.0

- **完整协议支持** - 所有 MQTT 5.0 特性
- **TLS 加密** - 安全的传输层加密
- **QoS 支持** - 三种服务质量级别
- **会话持久化** - 断线重连和消息恢复

### CoAP

- **轻量级协议** - 适合资源受限设备
- **DTLS 安全** - 数据报传输层安全
- **观察模式** - 实时数据订阅
- **块传输** - 大数据分块传输

### LwM2M

- **设备管理** - 完整的设备生命周期管理
- **对象建模** - 标准化的设备对象模型
- **安全引导** - 安全的设备注册和认证
- **固件更新** - 安全的 OTA 升级

### OPC UA

- **工业标准** - 工业自动化通信标准
- **安全通信** - 内置的安全机制
- **信息模型** - 丰富的设备信息模型
- **订阅机制** - 高效的数据订阅

## 🚀 边缘计算

### 云边协同

- **智能调度** - 基于负载和延迟的任务调度
- **数据本地化** - 敏感数据本地处理
- **边缘缓存** - 智能的边缘数据缓存
- **故障转移** - 自动的故障检测和转移

### 资源管理

- **动态分配** - 基于需求的资源动态分配
- **负载均衡** - 智能的负载均衡算法
- **资源监控** - 实时的资源使用监控
- **容量规划** - 基于历史数据的容量规划

### 数据处理

- **流式处理** - 实时数据流处理
- **批处理** - 高效的数据批处理
- **机器学习** - 边缘 AI 推理
- **数据压缩** - 智能的数据压缩算法

## 📊 可观测性

### 指标收集

- **Prometheus 集成** - 标准的指标收集和存储
- **自定义指标** - 业务相关的自定义指标
- **指标聚合** - 多维度指标聚合
- **指标导出** - 多种格式的指标导出

### 分布式追踪

- **OpenTelemetry** - 标准的分布式追踪
- **链路追踪** - 完整的请求链路追踪
- **上下文传播** - 跨服务的上下文传播
- **性能分析** - 详细的性能分析

### 告警系统

- **智能告警** - 基于规则的智能告警
- **告警升级** - 自动的告警升级机制
- **告警抑制** - 防止告警风暴
- **告警通知** - 多种通知方式

## 🎓 教育价值

### 学习路径

1. **基础概念** - 从 IoT 基本概念开始
2. **通信协议** - 学习各种 IoT 通信协议
3. **安全机制** - 掌握 IoT 安全最佳实践
4. **边缘计算** - 理解边缘计算架构
5. **可观测性** - 学习监控和告警

### 实践项目

- **智能家居** - 完整的智能家居系统
- **工业监控** - 工业设备监控系统
- **环境监测** - 环境数据采集系统
- **设备管理** - 大规模设备管理系统

### 参考资料

- **国际标准** - ISO/IEC、IEC、NIST 标准
- **大学研究** - MIT、Stanford、Berkeley 研究成果
- **开源项目** - 相关开源项目参考
- **最佳实践** - 行业最佳实践指南

## 🌟 创新亮点

### 技术创新

- **2025 年标准对标** - 完全符合最新国际标准
- **大学研究成果集成** - 融合顶级大学最新研究
- **Rust 语言优势** - 充分利用 Rust 的安全性和性能
- **模块化架构** - 高度模块化和可扩展的设计

### 架构创新

- **云边协同** - 创新的云边协同架构
- **安全优先** - 安全优先的设计理念
- **可观测性** - 完整的可观测性体系
- **隐私保护** - 先进的隐私保护技术

### 生态创新

- **开源协作** - 开放和协作的开发模式
- **标准兼容** - 遵循国际标准和最佳实践
- **社区驱动** - 基于社区反馈的持续改进
- **教育友好** - 专为教育场景优化的设计

## 📞 支持与贡献

### 获取支持

- 问题报告: [GitHub Issues](https://github.com/rust-lang/c17_iot/issues)
- 讨论区: [GitHub Discussions](https://github.com/rust-lang/c17_iot/discussions)
- 文档: [GitHub Wiki](https://github.com/rust-lang/c17_iot/wiki)

### 贡献指南

1. Fork 项目
2. 创建功能分支
3. 编写代码和测试
4. 提交 Pull Request
5. 参与代码审查

### 贡献类型

- 功能开发 - 新功能的实现
- 性能优化 - 性能改进和优化
- 文档完善 - 文档的改进和补充
- 测试增强 - 测试覆盖率的提高
- 安全改进 - 安全机制的增强

## 📄 许可证

本项目采用 MIT 许可证。详见 [LICENSE](LICENSE) 文件。

---

**Rust IoT 系统** - 让物联网开发更简单、更安全、更高效！

**Rust IoT System** - Making IoT development simpler, safer, and more efficient!
