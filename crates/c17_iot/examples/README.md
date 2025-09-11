# c17_iot Examples 指南

## 运行前置

- Rust toolchain 已安装；在 `crates/c17_iot` 下运行命令
- 可选服务：MQTT/MQTT-TLS、CoAP、Kafka、InfluxDB、Prometheus/Grafana

## 快速运行

```bash
cargo run --example ota_simulate
cargo run --example ditto_shadow
cargo run --example edge_ingest
cargo run --example otel_stdout
cargo run --example prom_stdout
```

## 协议与安全

- MQTT：
  - 明文: `cargo run --example mqtt_minimal`（需 1883 broker）
  - TLS 演示: `cargo run --example mqtt_tls`
  - TLS 严格校验: `cargo run --example mqtt_tls_strict`（先执行 `scripts/gen_certs.(ps1|sh)` 生成 `examples/certs/*` 并配置 Broker）
- CoAP：
  - 明文: `cargo run --example coap_observe`（需本地 5683 server）
  - DTLS 占位: `cargo run --example coap_dtls`

## 可观测性与数据

- Prometheus 导出：`cargo run --example prom_exporter_http` → <http://127.0.0.1:9898/metrics>
- Kafka 生产者：`cargo run --example kafka_producer`（需 `localhost:9092`）
- InfluxDB 写入：
  - 环境变量：`INFLUX_URL` `INFLUX_ORG` `INFLUX_BUCKET` `INFLUX_TOKEN`
  - 运行：`cargo run --example influx_write`

## 设备建模

- LwM2M：`cargo run --example lwm2m_minimal`
- OPC UA：`cargo run --example opcua_gateway_mock`

## Docker 联调

参见 `examples/_compose/docker-compose.yml`，一键起服务。
默认包含：Mosquitto、Zookeeper、Kafka、InfluxDB、Telegraf、Grafana、Jaeger。
Grafana 预置 Influx 数据源与简单看板（环境变量需提供 `INFLUX_ORG/INFLUX_BUCKET/INFLUX_TOKEN`）。

## SBOM 与证书

- 生成 SBOM（CycloneDX）：`scripts/gen_sbom.(ps1|sh)` → `sbom.json`
- 生成测试证书（自签）：`scripts/gen_certs.(ps1|sh)` → `examples/certs/`
