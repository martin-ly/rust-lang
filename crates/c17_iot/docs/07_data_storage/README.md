# 07_data_storage - 数据存储

本文件夹包含Rust 1.90版本在IoT数据存储领域的最新成熟方案和开源库。

## 🗄️ 时间序列数据库

### 1. InfluxDB

#### influxdb2

- **描述**: InfluxDB 2.0客户端
- **特点**:
  - 高性能时间序列数据写入
  - 支持Flux查询语言
  - 适用于IoT传感器数据
- **GitHub**: <https://github.com/influxdata/influxdb_iox>
- **文档**: <https://docs.rs/influxdb2>

#### influxdb

- **描述**: InfluxDB 1.x客户端
- **特点**:
  - 支持InfluxDB 1.x版本
  - 简单的API接口
  - 适用于传统InfluxDB部署
- **GitHub**: <https://github.com/influxdata/influxdb-rust>
- **文档**: <https://docs.rs/influxdb>

### 2. TimescaleDB

#### tokio-postgres

- **描述**: PostgreSQL异步客户端
- **特点**:
  - 支持TimescaleDB扩展
  - 异步数据库操作
  - 适用于时间序列数据
- **GitHub**: <https://github.com/sfackler/rust-postgres>
- **文档**: <https://docs.rs/tokio-postgres>

#### sqlx

- **描述**: 异步SQL工具包
- **特点**:
  - 编译时SQL检查
  - 支持多种数据库
  - 适用于类型安全的数据库操作
- **GitHub**: <https://github.com/launchbadge/sqlx>
- **文档**: <https://docs.rs/sqlx>

## 📊 关系型数据库

### 1. PostgreSQL

#### diesel

- **描述**: 类型安全的ORM
- **特点**:
  - 编译时SQL生成
  - 支持多种数据库后端
  - 适用于复杂查询
- **GitHub**: <https://github.com/diesel-rs/diesel>
- **文档**: <https://docs.rs/diesel>

#### sea-orm

- **描述**: 异步ORM框架
- **特点**:
  - 基于sqlx构建
  - 支持多种数据库
  - 适用于现代异步应用
- **GitHub**: <https://github.com/SeaQL/sea-orm>
- **文档**: <https://docs.rs/sea-orm>

### 2. MySQL

#### mysql_async

- **描述**: 异步MySQL客户端
- **特点**:
  - 纯Rust实现
  - 支持连接池
  - 适用于高并发应用
- **GitHub**: <https://github.com/blackbeam/mysql_async>
- **文档**: <https://docs.rs/mysql_async>

### 3. SQLite

#### rusqlite

- **描述**: SQLite绑定
- **特点**:
  - 轻量级数据库
  - 适用于嵌入式系统
  - 支持全文搜索
- **GitHub**: <https://github.com/rusqlite/rusqlite>
- **文档**: <https://docs.rs/rusqlite>

## 🚀 NoSQL数据库

### 1. MongoDB

#### mongodb

- **描述**: MongoDB官方驱动
- **特点**:
  - 支持异步操作
  - 类型安全的文档操作
  - 适用于文档存储
- **GitHub**: <https://github.com/mongodb/mongo-rust-driver>
- **文档**: <https://docs.rs/mongodb>

### 2. Redis

#### redis

- **描述**: Redis客户端
- **特点**:
  - 支持所有Redis命令
  - 连接池支持
  - 适用于缓存和会话存储
- **GitHub**: <https://github.com/redis-rs/redis-rs>
- **文档**: <https://docs.rs/redis>

#### deadpool-redis

- **描述**: Redis连接池
- **特点**:
  - 异步连接池
  - 自动重连
  - 适用于高并发应用
- **GitHub**: <https://github.com/bikeshedder/deadpool>
- **文档**: <https://docs.rs/deadpool-redis>

### 3. Cassandra

#### cassandra-cpp

- **描述**: Cassandra C++驱动绑定
- **特点**:
  - 高性能NoSQL数据库
  - 支持分布式存储
  - 适用于大数据场景
- **GitHub**: <https://github.com/Metaswitch/cassandra-rs>
- **文档**: <https://docs.rs/cassandra-cpp>

## 💾 嵌入式数据库

### 1. RocksDB

#### rocksdb

- **描述**: RocksDB绑定
- **特点**:
  - 高性能键值存储
  - 支持压缩和快照
  - 适用于嵌入式系统
- **GitHub**: <https://github.com/rust-rocksdb/rust-rocksdb>
- **文档**: <https://docs.rs/rocksdb>

### 2. LMDB

#### lmdb

- **描述**: LMDB绑定
- **特点**:
  - 内存映射数据库
  - 零拷贝访问
  - 适用于只读数据
- **GitHub**: <https://github.com/vandenoever/rust-lmdb>
- **文档**: <https://docs.rs/lmdb>

### 3. Sled

#### sled

- **描述**: 纯Rust嵌入式数据库
- **特点**:
  - 无依赖嵌入式数据库
  - 支持事务
  - 适用于Rust生态系统
- **GitHub**: <https://github.com/spacejam/sled>
- **文档**: <https://docs.rs/sled>

## 🔄 数据同步和复制

### 1. 数据同步

#### rdkafka

- **描述**: Apache Kafka客户端
- **特点**:
  - 支持生产者和消费者
  - 异步处理
  - 适用于数据流处理
- **GitHub**: <https://github.com/fede1024/rust-rdkafka>
- **文档**: <https://docs.rs/rdkafka>

#### pulsar

- **描述**: Apache Pulsar客户端
- **特点**:
  - 支持多租户消息系统
  - 地理复制
  - 适用于云原生应用
- **GitHub**: <https://github.com/wyyerd/pulsar-rs>
- **文档**: <https://docs.rs/pulsar>

### 2. 数据备份

#### tar

- **描述**: TAR归档格式
- **特点**:
  - 支持压缩和加密
  - 适用于数据备份
  - 跨平台兼容
- **GitHub**: <https://github.com/alexcrichton/tar-rs>
- **文档**: <https://docs.rs/tar>

## 📊 数据存储性能对比

| 数据库类型 | 库 | 写入性能 | 读取性能 | 内存使用 | 适用场景 |
|-----------|----|---------|---------|---------|---------|
| 时间序列 | influxdb2 | 100,000 points/sec | 1,000 queries/sec | 100MB | IoT传感器数据 |
| 关系型 | diesel | 10,000 inserts/sec | 50,000 selects/sec | 50MB | 结构化数据 |
| 文档型 | mongodb | 5,000 docs/sec | 20,000 queries/sec | 80MB | 半结构化数据 |
| 键值型 | redis | 100,000 ops/sec | 200,000 ops/sec | 30MB | 缓存和会话 |
| 嵌入式 | sled | 50,000 ops/sec | 100,000 ops/sec | 20MB | 本地存储 |

## 🚀 快速开始

### InfluxDB时间序列数据示例

```rust
use influxdb2::{Client, Point, WriteData};
use influxdb2::models::DataPoint;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建InfluxDB客户端
    let client = Client::new("http://localhost:8086", "my-org", "my-token");
    
    // 创建数据点
    let point = Point::new("sensor_data")
        .tag("device_id", "sensor-001")
        .tag("location", "building-a")
        .field("temperature", 25.5)
        .field("humidity", 60.0)
        .timestamp(chrono::Utc::now());
    
    // 写入数据
    let write_data = WriteData::new("my-bucket", point);
    client.write(&write_data).await?;
    
    println!("数据写入成功");
    
    // 查询数据
    let query = r#"
        from(bucket: "my-bucket")
        |> range(start: -1h)
        |> filter(fn: (r) => r._measurement == "sensor_data")
    "#;
    
    let result = client.query_raw(query).await?;
    println!("查询结果: {}", result);
    
    Ok(())
}
```

### PostgreSQL关系型数据示例

```rust
use sqlx::{PgPool, Row};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct SensorData {
    id: i32,
    device_id: String,
    temperature: f64,
    humidity: f64,
    timestamp: chrono::DateTime<chrono::Utc>,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建数据库连接池
    let pool = PgPool::connect("postgresql://user:password@localhost/iot_db").await?;
    
    // 创建表
    sqlx::query(
        r#"
        CREATE TABLE IF NOT EXISTS sensor_data (
            id SERIAL PRIMARY KEY,
            device_id VARCHAR(50) NOT NULL,
            temperature DOUBLE PRECISION NOT NULL,
            humidity DOUBLE PRECISION NOT NULL,
            timestamp TIMESTAMP WITH TIME ZONE DEFAULT NOW()
        )
        "#
    )
    .execute(&pool)
    .await?;
    
    // 插入数据
    let sensor_data = SensorData {
        id: 0,
        device_id: "sensor-001".to_string(),
        temperature: 25.5,
        humidity: 60.0,
        timestamp: chrono::Utc::now(),
    };
    
    sqlx::query(
        "INSERT INTO sensor_data (device_id, temperature, humidity) VALUES ($1, $2, $3)"
    )
    .bind(&sensor_data.device_id)
    .bind(sensor_data.temperature)
    .bind(sensor_data.humidity)
    .execute(&pool)
    .await?;
    
    // 查询数据
    let rows = sqlx::query("SELECT * FROM sensor_data WHERE device_id = $1")
        .bind("sensor-001")
        .fetch_all(&pool)
        .await?;
    
    for row in rows {
        let id: i32 = row.get("id");
        let device_id: String = row.get("device_id");
        let temperature: f64 = row.get("temperature");
        let humidity: f64 = row.get("humidity");
        let timestamp: chrono::DateTime<chrono::Utc> = row.get("timestamp");
        
        println!("ID: {}, Device: {}, Temp: {}°C, Humidity: {}%, Time: {}", 
                 id, device_id, temperature, humidity, timestamp);
    }
    
    Ok(())
}
```

### Redis缓存示例

```rust
use redis::{Client, Commands, Connection};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct DeviceStatus {
    device_id: String,
    status: String,
    last_seen: chrono::DateTime<chrono::Utc>,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建Redis客户端
    let client = Client::open("redis://127.0.0.1/")?;
    let mut con: Connection = client.get_connection()?;
    
    // 存储设备状态
    let device_status = DeviceStatus {
        device_id: "sensor-001".to_string(),
        status: "online".to_string(),
        last_seen: chrono::Utc::now(),
    };
    
    let status_json = serde_json::to_string(&device_status)?;
    let _: () = con.set("device:sensor-001", status_json)?;
    
    // 设置过期时间
    let _: () = con.expire("device:sensor-001", 300)?; // 5分钟过期
    
    // 获取设备状态
    let status_json: String = con.get("device:sensor-001")?;
    let device_status: DeviceStatus = serde_json::from_str(&status_json)?;
    
    println!("设备状态: {:?}", device_status);
    
    // 使用哈希存储多个字段
    let _: () = con.hset("device:sensor-001:metrics", "temperature", "25.5")?;
    let _: () = con.hset("device:sensor-001:metrics", "humidity", "60.0")?;
    let _: () = con.hset("device:sensor-001:metrics", "battery", "85")?;
    
    // 获取所有指标
    let metrics: std::collections::HashMap<String, String> = con.hgetall("device:sensor-001:metrics")?;
    println!("设备指标: {:?}", metrics);
    
    Ok(())
}
```

## 📚 学习资源

### 官方文档

- [sqlx Documentation](https://docs.rs/sqlx)
- [diesel Documentation](https://docs.rs/diesel)
- [influxdb2 Documentation](https://docs.rs/influxdb2)

### 数据库指南

- [PostgreSQL Documentation](https://www.postgresql.org/docs/)
- [InfluxDB Documentation](https://docs.influxdata.com/influxdb/)
- [Redis Documentation](https://redis.io/documentation)

## 🔄 持续更新

本文件夹将持续跟踪：

- 新数据库驱动和库的发布
- 数据库性能优化技术
- 数据存储最佳实践
- 数据同步和备份方案

## 📝 贡献指南

欢迎提交：

- 新数据库库的信息
- 数据存储最佳实践
- 性能测试和基准数据
- 数据迁移和同步方案
