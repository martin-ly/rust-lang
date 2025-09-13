# c17_iot

Rust IoT 示例与参考实现，基于2025年IoT行业标准架构设计，对标国际著名大学研究成果。覆盖通信（MQTT/CoAP/TLS）、设备建模（LwM2M/OPC UA）、可观测性（Prom/OTEL/Jaeger）、边缘计算、安全框架、隐私保护、数据管道（Kafka/InfluxDB）。

## 🚀 2025年标准对标特性

- **国际标准支持**：ISO/IEC 30141、IEC 62443、NIST IoT基线
- **大学研究成果**：MIT边缘智能、Stanford隐私保护、Berkeley分布式系统
- **增强安全框架**：TLS 1.3、DTLS、OSCORE、X.509证书管理
- **边缘计算增强**：云边协同、智能调度、资源管理
- **可观测性完善**：OpenTelemetry、Prometheus、智能告警
- **隐私保护**：零知识证明、差分隐私、安全多方计算

## 快速开始

```bash
cargo test -p c17_iot
cargo run -p c17_iot --example prom_exporter_http
```

更多示例与依赖参见 `examples/`，以及每个示例文件内注释。

## 目录

- `src/`：核心模块（嵌入式/HAL、调度、功耗、工具、类型）
- `examples/`：最小可运行示例
- `scripts/`：一键脚本（Windows/Linux）

## 特性开关（features）

在 `crates/c17_iot/Cargo.toml` 中：

- `kafka`：启用 Kafka 示例，依赖 `rdkafka`
- `influx`：启用 InfluxDB 示例，依赖 `influxdb2`
- `openssl-examples`：启用基于 OpenSSL 的示例（如 CoAP DTLS）

启用特性示例：

```bash
cargo run -p c17_iot --example kafka_producer --features kafka
```

## 示例清单与运行

下列示例大多可通过环境变量进行参数化，未设置时使用安全默认值。

### 同步示例

- LwM2M 最小对象建模：

  ```bash
  cargo run -p c17_iot --example lwm2m_minimal
  ```

- OPC UA 网关对象读写模拟：

  ```bash
  cargo run -p c17_iot --example opcua_gateway_mock
  ```

- OTA 升级模拟（哈希校验、写入、回滚）：

  ```bash
  cargo run -p c17_iot --example ota_simulate
  ```

- OpenTelemetry（stdout provider）：

  ```bash
  cargo run -p c17_iot --example otel_stdout
  ```

### 异步示例（Tokio）

- MQTT 最小示例（`rumqttc`）：

  ```bash
  # 需要本地 MQTT Broker：localhost:1883
  cargo run -p c17_iot --example mqtt_minimal
  ```
  
  - 环境变量：`MQTT_HOST`、`MQTT_PORT`、`MQTT_CLIENT_ID`、`MQTT_SUB`、`MQTT_PUB`、`MQTT_QOS`、`ITER`、`POLL_TIMEOUT_MS`

- MQTT TLS（演示 Simple TLS，跳过证书校验）：

  ```bash
  # 需要 TLS MQTT Broker：localhost:8883
  cargo run -p c17_iot --example mqtt_tls
  ```
  
  - 环境变量：同上

- MQTT TLS 严格（可加载 CA 文件）：

  ```bash
  # 需要 TLS MQTT Broker：localhost:8883
  CA_PATH=./examples/certs/ca.crt cargo run -p c17_iot --example mqtt_tls_strict
  ```
  
  - 环境变量：`CA_PATH`、以及 MQTT 基本连接变量同上

- Prometheus Exporter（HTTP /metrics）：

  ```bash
  cargo run -p c17_iot --example prom_exporter_http
  # 打开 http://127.0.0.1:9898/metrics，Ctrl+C 优雅退出
  ```

- OpenTelemetry OTLP → Jaeger（gRPC 4317）：

  ```bash
  # 默认 http://127.0.0.1:4317
  OTLP_ENDPOINT=http://127.0.0.1:4317 OTLP_SHUTDOWN_MS=800 \
  cargo run -p c17_iot --example otel_jaeger
  ```

- Kafka 生产者（需启用特性 `kafka`）：

  ```bash
  cargo run -p c17_iot --example kafka_producer --features kafka
  # 可选环境变量：
  # BROKER, TOPIC, KEY, COUNT, TIMEOUT_MS, SEND_AWAIT_MS, MAX_RETRIES
  ```

## 环境变量速查

- MQTT：`MQTT_HOST`、`MQTT_PORT`、`MQTT_CLIENT_ID`、`MQTT_SUB`、`MQTT_PUB`、`MQTT_QOS`、`ITER`、`POLL_TIMEOUT_MS`
- MQTT TLS 严格：额外 `CA_PATH`
- Kafka：`BROKER`、`TOPIC`、`KEY`、`COUNT`、`TIMEOUT_MS`、`SEND_AWAIT_MS`、`MAX_RETRIES`
- OTLP Jaeger：`OTLP_ENDPOINT`、`OTLP_SHUTDOWN_MS`

## 依赖服务清单

- MQTT/MQTT-TLS：本地或远端 Broker（1883/8883）
- Kafka：Broker（默认 `localhost:9092`）
- Prometheus：浏览器或 `curl` 拉取 `/metrics`
- OTLP/Jaeger：OTLP gRPC 端点（默认 `http://127.0.0.1:4317`）

## 注意事项

- TLS 示例中的 Simple TLS 仅用于演示便捷编译运行。生产环境请加载 CA/证书，并启用严格校验、主机名验证及双向认证（如需要）。
- 示例默认超时时间较短，部署到网络延迟较高环境时请调整相关环境变量。
