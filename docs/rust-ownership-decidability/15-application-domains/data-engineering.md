# Rust 数据工程

数据工程领域对性能和可靠性有极高要求，Rust 的高性能和内存安全特性使其成为数据处理、流计算、数据库开发的理想选择。
本文档深入介绍 Rust 在数据工程领域的应用。

## 目录

- [Rust 数据工程](#rust-数据工程)
  - [目录](#目录)
  - [数据工程概述](#数据工程概述)
    - [Rust 在数据工程中的优势](#rust-在数据工程中的优势)
    - [生态概览](#生态概览)
  - [数据处理框架](#数据处理框架)
    - [Polars 高性能 DataFrame](#polars-高性能-dataframe)
    - [DataFusion 查询引擎](#datafusion-查询引擎)
  - [流处理](#流处理)
    - [Tokio 流处理管道](#tokio-流处理管道)
    - [Fluvio/Kafka 集成](#fluviokafka-集成)
  - [数据库开发](#数据库开发)
    - [嵌入式数据库](#嵌入式数据库)
    - [列式存储引擎](#列式存储引擎)
  - [序列化与存储格式](#序列化与存储格式)
    - [Apache Arrow](#apache-arrow)
    - [Parquet 列式存储](#parquet-列式存储)
  - [ETL 管道](#etl-管道)
    - [完整 ETL 实现](#完整-etl-实现)
  - [实时分析](#实时分析)
    - [实时指标计算](#实时指标计算)
  - [最佳实践](#最佳实践)
    - [1. 内存管理](#1-内存管理)
    - [2. 并发处理](#2-并发处理)
    - [3. 错误处理](#3-错误处理)
  - [总结](#总结)

---

## 数据工程概述

### Rust 在数据工程中的优势

| 特性 | Rust 实现 | Python/Pandas 对比 | Java/Spark 对比 |
|------|-----------|-------------------|-----------------|
| 性能 | 原生性能，无 GC | 快 10-100 倍 | 快 2-5 倍 |
| 内存占用 | 极低 | 1/10 - 1/100 | 1/2 - 1/5 |
| 类型安全 | 编译时保证 | 运行时检查 | 编译时检查 |
| 并发 | fearless 并发 | GIL 限制 | 线程安全 |
| 零拷贝 | 天然支持 | 不支持 | 部分支持 |

### 生态概览

| 类别 | 主要 Crate | 用途 |
|------|-----------|------|
| DataFrame | Polars, DataFusion | 数据处理、分析 |
| 流处理 | Tokio, Fluvio, Vector | 实时数据流 |
| 序列化 | Arrow, Parquet, Avro | 列式存储 |
| 数据库 | SQLx, Diesel, SeaORM | 数据库交互 |
| 存储 | RocksDB, Sled | 嵌入式存储 |

---

## 数据处理框架

### Polars 高性能 DataFrame

```rust
//! Polars 数据处理完整示例

use polars::prelude::*;
use std::time::Instant;
use rand::{thread_rng, Rng};
use rand::distributions::{Alphanumeric, Uniform};

/// 生成示例数据
pub fn generate_sales_data(n: usize) -> Result<DataFrame, PolarsError> {
    let mut rng = thread_rng();

    // 生成产品 ID
    let product_ids: Vec<i64> = (0..n).map(|_| rng.gen_range(1..=1000)).collect();

    // 生成分类
    let categories = vec!["Electronics", "Clothing", "Food", "Books", "Home"];
    let category_vec: Vec<String> = (0..n)
        .map(|_| categories[rng.gen_range(0..categories.len())].to_string())
        .collect();

    // 生成金额
    let amount_dist = Uniform::new(10.0, 1000.0);
    let amounts: Vec<f64> = (0..n).map(|_| rng.sample(amount_dist)).collect();

    // 生成数量
    let quantities: Vec<i32> = (0..n).map(|_| rng.gen_range(1..=100)).collect();

    // 生成日期
    let dates: Vec<i64> = (0..n)
        .map(|_| {
            let days_ago = rng.gen_range(0..365);
            let base = 1704067200000i64; // 2024-01-01
            base - days_ago as i64 * 86400000
        })
        .collect();

    // 生成地区
    let regions = vec!["North", "South", "East", "West", "Central"];
    let region_vec: Vec<String> = (0..n)
        .map(|_| regions[rng.gen_range(0..regions.len())].to_string())
        .collect();

    df! {
        "product_id" => product_ids,
        "category" => category_vec,
        "amount" => amounts,
        "quantity" => quantities,
        "date" => dates,
        "region" => region_vec,
    }
}

/// 数据处理示例
pub struct DataProcessor;

impl DataProcessor {
    /// 加载 CSV 数据
    pub fn from_csv(path: &str) -> Result<DataFrame, PolarsError> {
        CsvReadOptions::default()
            .try_into_reader_with_file_path(Some(path.into()))?
            .finish()
    }

    /// 数据清洗
    pub fn clean_data(df: &mut DataFrame) -> Result<&mut DataFrame, PolarsError> {
        // 移除空值
        *df = df.drop_nulls(None)?;

        // 移除重复行
        *df = df.unique(None, UniqueKeepStrategy::First, None)?;

        // 数据类型转换
        if df.column("amount").is_ok() {
            *df = df.with_column(
                col("amount").cast(DataType::Float64)
            )?;
        }

        // 添加计算列
        *df = df.with_column(
            (col("amount") * col("quantity")).alias("total")
        )?;

        Ok(df)
    }

    /// 聚合分析
    pub fn aggregate_by_category(df: &DataFrame) -> Result<DataFrame, PolarsError> {
        df.clone()
            .lazy()
            .group_by([col("category")])
            .agg([
                col("amount").sum().alias("total_amount"),
                col("amount").mean().alias("avg_amount"),
                col("quantity").sum().alias("total_quantity"),
                col("product_id").count().alias("transaction_count"),
                col("total").sum().alias("grand_total"),
            ])
            .sort(["total_amount"], SortMultipleOptions::default().with_order_descending(true))
            .collect()
    }

    /// 多维度分析
    pub fn pivot_analysis(df: &DataFrame) -> Result<DataFrame, PolarsError> {
        df.clone()
            .lazy()
            .group_by([col("region"), col("category")])
            .agg([
                col("total").sum().alias("sales")
            ])
            .collect()?
            .pivot(["region"], Some(["category"]), Some(["sales"]), false, None, None)?
    }

    /// 时间序列分析
    pub fn time_series_analysis(df: &DataFrame) -> Result<DataFrame, PolarsError> {
        df.clone()
            .lazy()
            .with_column(
                (col("date") / lit(1000)).cast(DataType::Datetime(TimeUnit::Milliseconds, None))
            )
            .group_by_dynamic(
                col("date"),
                [],
                DynamicGroupOptions {
                    every: Duration::parse("1d"),
                    period: Duration::parse("1d"),
                    offset: Duration::parse("0d"),
                    truncate: true,
                    include_boundaries: false,
                    closed_window: ClosedWindow::Left,
                    start_by: StartBy::DataPoint,
                    ..Default::default()
                }
            )
            .agg([
                col("total").sum().alias("daily_sales"),
                col("quantity").sum().alias("daily_quantity"),
                col("product_id").count().alias("transaction_count"),
            ])
            .with_column(
                col("daily_sales")
                    .rolling_mean(RollingOptions {
                        window_size: Duration::parse("7d"),
                        min_periods: 1,
                        weights: None,
                        center: false,
                        by: None,
                        fn_params: Default::default(),
                    })
                    .alias("weekly_avg")
            )
            .collect()
    }

    /// 窗口函数分析
    pub fn window_analysis(df: &DataFrame) -> Result<DataFrame, PolarsError> {
        df.clone()
            .lazy()
            .with_columns([
                col("amount")
                    .rank(
                        RankOptions {
                            method: RankMethod::Dense,
                            descending: true,
                        },
                        None,
                    )
                    .over([col("category")])
                    .alias("rank_in_category"),

                col("total")
                    .sum()
                    .over([col("category")])
                    .alias("category_total"),

                (col("total") / col("total").sum().over([col("category")]) * lit(100.0))
                    .alias("pct_of_category"),
            ])
            .collect()
    }

    /// 复杂查询示例
    pub fn complex_query(df: &DataFrame) -> Result<DataFrame, PolarsError> {
        let high_value_threshold = 500.0;

        df.clone()
            .lazy()
            .filter(
                col("amount").gt(lit(high_value_threshold))
                    .and(col("quantity").gt(lit(10)))
            )
            .with_column(
                when(col("category").eq(lit("Electronics")))
                    .then(lit("Tech"))
                    .when(col("category").eq(lit("Books")))
                    .then(lit("Media"))
                    .otherwise(lit("Other"))
                    .alias("category_group")
            )
            .group_by([col("category_group"), col("region")])
            .agg([
                col("total").sum().alias("total_sales"),
                col("total").mean().alias("avg_sales"),
                col("total").count().alias("count"),
                col("total").quantile(lit(0.95), QuantileInterpolOptions::default()).alias("p95_sales"),
            ])
            .filter(col("count").gt(lit(10)))
            .sort(["total_sales"], SortMultipleOptions::default().with_order_descending(true))
            .limit(100)
            .collect()
    }

    /// 数据导出
    pub fn export_to_parquet(df: &DataFrame, path: &str) -> Result<(), PolarsError> {
        let mut file = std::fs::File::create(path)?;
        ParquetWriter::new(&mut file).finish(df)?;
        Ok(())
    }

    pub fn export_to_json(df: &DataFrame, path: &str) -> Result<(), PolarsError> {
        let mut file = std::fs::File::create(path)?;
        JsonWriter::new(&mut file).finish(df)?;
        Ok(())
    }
}

/// 性能对比示例
pub fn benchmark() {
    println!("Generating 1 million records...");
    let start = Instant::now();
    let mut df = generate_sales_data(1_000_000).unwrap();
    println!("Generation took: {:?}", start.elapsed());

    println!("Running aggregation...");
    let start = Instant::now();
    let result = DataProcessor::aggregate_by_category(&df).unwrap();
    println!("Aggregation took: {:?}", start.elapsed());
    println!("{:?}", result);
}
```

### DataFusion 查询引擎

```rust
//! DataFusion 分布式查询引擎

use datafusion::prelude::*;
use datafusion::datasource::file_format::parquet::ParquetFormat;
use datafusion::datasource::listing::ListingOptions;
use std::sync::Arc;

pub struct QueryEngine {
    ctx: SessionContext,
}

impl QueryEngine {
    pub async fn new() -> Result<Self, DataFusionError> {
        let config = SessionConfig::new()
            .with_target_partitions(8)
            .with_batch_size(8192);

        let ctx = SessionContext::new_with_config(config);

        Ok(Self { ctx })
    }

    /// 注册 Parquet 数据源
    pub async fn register_parquet(&self, name: &str, path: &str) -> Result<(), DataFusionError> {
        let listing_options = ListingOptions::new(Arc::new(ParquetFormat::default()));

        self.ctx
            .register_listing_table(name, path, listing_options, None, None)
            .await?;

        Ok(())
    }

    /// 注册 CSV 数据源
    pub async fn register_csv(&self, name: &str, path: &str) -> Result<(), DataFusionError> {
        self.ctx.register_csv(name, path, CsvReadOptions::new()).await?;
        Ok(())
    }

    /// 执行 SQL 查询
    pub async fn query(&self, sql: &str) -> Result<DataFrame, DataFusionError> {
        self.ctx.sql(sql).await
    }

    /// 示例：销售分析
    pub async fn sales_analysis(&self) -> Result<DataFrame, DataFusionError> {
        self.ctx.sql(r#"
            SELECT
                category,
                region,
                SUM(amount) as total_sales,
                AVG(amount) as avg_sales,
                COUNT(*) as transaction_count,
                PERCENTILE_CONT(0.95) WITHIN GROUP (ORDER BY amount) as p95_amount
            FROM sales
            WHERE date >= '2024-01-01'
            GROUP BY category, region
            HAVING SUM(amount) > 10000
            ORDER BY total_sales DESC
        "#).await
    }

    /// 示例：时间窗口分析
    pub async fn time_window_analysis(&self) -> Result<DataFrame, DataFusionError> {
        self.ctx.sql(r#"
            SELECT
                DATE_TRUNC('month', date) as month,
                category,
                SUM(amount) as monthly_sales,
                LAG(SUM(amount)) OVER (PARTITION BY category ORDER BY DATE_TRUNC('month', date)) as prev_month_sales,
                (SUM(amount) - LAG(SUM(amount)) OVER (PARTITION BY category ORDER BY DATE_TRUNC('month', date)))
                    / NULLIF(LAG(SUM(amount)) OVER (PARTITION BY category ORDER BY DATE_TRUNC('month', date)), 0) * 100 as growth_pct
            FROM sales
            GROUP BY DATE_TRUNC('month', date), category
            ORDER BY month, category
        "#).await
    }

    /// 写入 Parquet
    pub async fn write_parquet(&self, df: &DataFrame, path: &str) -> Result<(), DataFusionError> {
        df.write_parquet(path, None).await?;
        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<(), DataFusionError> {
    let engine = QueryEngine::new().await?;

    // 注册数据源
    engine.register_parquet("sales", "data/sales").await?;
    engine.register_csv("customers", "data/customers.csv").await?;

    // 执行查询
    let df = engine.query(r#"
        SELECT s.*, c.customer_name
        FROM sales s
        JOIN customers c ON s.customer_id = c.id
        WHERE s.amount > 1000
        LIMIT 100
    "#).await?;

    df.show().await?;

    Ok(())
}
```

---

## 流处理

### Tokio 流处理管道

```rust
//! 实时流处理管道

use tokio::sync::mpsc;
use tokio::time::{interval, Duration, Instant};
use serde::{Serialize, Deserialize};
use std::collections::HashMap;
use dashmap::DashMap;

/// 原始事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RawEvent {
    pub timestamp: u64,
    pub user_id: String,
    pub event_type: String,
    pub data: serde_json::Value,
}

/// 处理后的记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessedRecord {
    pub timestamp: u64,
    pub window_start: u64,
    pub window_end: u64,
    pub user_id: String,
    pub event_type: String,
    pub metrics: EventMetrics,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct EventMetrics {
    pub count: u64,
    pub sum_value: f64,
    pub avg_value: f64,
    pub min_value: f64,
    pub max_value: f64,
}

/// 流处理管道
pub struct StreamPipeline {
    input_tx: mpsc::Sender<RawEvent>,
    output_rx: mpsc::Receiver<ProcessedRecord>,
}

impl StreamPipeline {
    pub fn new(buffer_size: usize) -> Self {
        let (input_tx, input_rx) = mpsc::channel(buffer_size);
        let (output_tx, output_rx) = mpsc::channel(buffer_size);

        // 启动处理任务
        tokio::spawn(Self::process_events(input_rx, output_tx));

        Self { input_tx, output_rx }
    }

    pub async fn send(&self, event: RawEvent) -> Result<(), mpsc::error::SendError<RawEvent>> {
        self.input_tx.send(event).await
    }

    pub async fn recv(&mut self) -> Option<ProcessedRecord> {
        self.output_rx.recv().await
    }

    /// 事件处理主循环
    async fn process_events(
        mut input_rx: mpsc::Receiver<RawEvent>,
        output_tx: mpsc::Sender<ProcessedRecord>,
    ) {
        // 窗口聚合状态
        let window_size_ms = 60000; // 1分钟窗口
        let mut window_aggregates: DashMap<(String, u64), EventMetrics> = DashMap::new();
        let mut last_flush = Instant::now();
        let mut flush_interval = interval(Duration::from_secs(10));

        loop {
            tokio::select! {
                Some(event) = input_rx.recv() => {
                    let window_key = Self::get_window_key(event.timestamp, window_size_ms);
                    let key = (event.user_id.clone(), window_key);

                    // 更新聚合
                    window_aggregates.entry(key).and_modify(|m| {
                        m.count += 1;
                        if let Some(value) = event.data.get("value").and_then(|v| v.as_f64()) {
                            m.sum_value += value;
                            m.avg_value = m.sum_value / m.count as f64;
                            m.min_value = m.min_value.min(value);
                            m.max_value = m.max_value.max(value);
                        }
                    }).or_insert_with(|| {
                        let mut m = EventMetrics {
                            count: 1,
                            sum_value: 0.0,
                            avg_value: 0.0,
                            min_value: f64::MAX,
                            max_value: f64::MIN,
                        };
                        if let Some(value) = event.data.get("value").and_then(|v| v.as_f64()) {
                            m.sum_value = value;
                            m.avg_value = value;
                            m.min_value = value;
                            m.max_value = value;
                        }
                        m
                    });
                }

                _ = flush_interval.tick() => {
                    // 刷新过期窗口
                    let current_window = Self::get_current_window(window_size_ms);

                    let records: Vec<ProcessedRecord> = window_aggregates
                        .iter()
                        .filter(|entry| entry.key().1 < current_window - window_size_ms)
                        .map(|entry| {
                            let (user_id, window_start) = entry.key().clone();
                            ProcessedRecord {
                                timestamp: current_window,
                                window_start,
                                window_end: window_start + window_size_ms,
                                user_id,
                                event_type: "aggregated".to_string(),
                                metrics: entry.value().clone(),
                            }
                        })
                        .collect();

                    // 发送记录并清理
                    for record in records {
                        let _ = output_tx.send(record).await;
                        window_aggregates.remove(&(record.user_id.clone(), record.window_start));
                    }
                }

                else => break,
            }
        }
    }

    fn get_window_key(timestamp: u64, window_size: u64) -> u64 {
        (timestamp / window_size) * window_size
    }

    fn get_current_window(window_size: u64) -> u64 {
        Self::get_window_key(
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_millis() as u64,
            window_size
        )
    }
}

/// 带背压的流处理器
pub struct BackpressureProcessor<T> {
    sender: mpsc::Sender<T>,
    receiver: mpsc::Receiver<T>,
    semaphore: Arc<tokio::sync::Semaphore>,
}

impl<T: Send + 'static> BackpressureProcessor<T> {
    pub fn new(capacity: usize, max_concurrent: usize) -> Self {
        let (sender, receiver) = mpsc::channel(capacity);
        let semaphore = Arc::new(tokio::sync::Semaphore::new(max_concurrent));

        Self { sender, receiver, semaphore }
    }

    pub async fn submit<F, Fut, R>(&self, item: T, processor: F) -> Result<R, mpsc::error::SendError<T>>
    where
        F: FnOnce(T) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = R> + Send,
        R: Send + 'static,
    {
        let (tx, rx) = tokio::sync::oneshot::channel();
        let permit = self.semaphore.clone().acquire_owned().await.unwrap();

        self.sender.send(item).await?;

        tokio::spawn(async move {
            let _permit = permit;
            // 处理逻辑...
        });

        rx.await.map_err(|_| panic!("Processor failed"))
    }
}
```

### Fluvio/Kafka 集成

```rust
//! Kafka 流处理集成

use rdkafka::config::ClientConfig;
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::message::Message;
use futures::StreamExt;

pub struct KafkaProcessor {
    consumer: StreamConsumer,
    producer: FutureProducer,
}

impl KafkaProcessor {
    pub fn new(brokers: &str, group_id: &str) -> Result<Self, rdkafka::error::KafkaError> {
        let consumer: StreamConsumer = ClientConfig::new()
            .set("bootstrap.servers", brokers)
            .set("group.id", group_id)
            .set("enable.auto.commit", "true")
            .set("auto.offset.reset", "earliest")
            .create()?;

        let producer: FutureProducer = ClientConfig::new()
            .set("bootstrap.servers", brokers)
            .set("message.timeout.ms", "5000")
            .create()?;

        Ok(Self { consumer, producer })
    }

    pub async fn subscribe(&self, topics: &[&str]) -> Result<(), rdkafka::error::KafkaError> {
        self.consumer.subscribe(topics)
    }

    pub async fn process_messages<F>(&self, mut handler: F) -> Result<(), Box<dyn std::error::Error>>
    where
        F: FnMut(&[u8]) -> Result<Vec<u8>, Box<dyn std::error::Error>>,
    {
        let mut stream = self.consumer.stream();

        while let Some(result) = stream.next().await {
            match result {
                Ok(msg) => {
                    if let Some(payload) = msg.payload() {
                        match handler(payload) {
                            Ok(processed) => {
                                // 发送到输出 topic
                                if let Some(key) = msg.key() {
                                    let record = FutureRecord::to("output-topic")
                                        .key(key)
                                        .payload(&processed);

                                    match self.producer.send(record, Duration::from_secs(5)).await {
                                        Ok(_) => println!("Message processed and sent"),
                                        Err(e) => eprintln!("Failed to send: {:?}", e),
                                    }
                                }
                            }
                            Err(e) => eprintln!("Processing error: {:?}", e),
                        }
                    }
                }
                Err(e) => eprintln!("Kafka error: {:?}", e),
            }
        }

        Ok(())
    }

    pub async fn send(&self, topic: &str, key: &str, payload: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
        let record = FutureRecord::to(topic)
            .key(key)
            .payload(payload);

        self.producer.send(record, Duration::from_secs(5)).await?;
        Ok(())
    }
}
```

---

## 数据库开发

### 嵌入式数据库

```rust
//! 嵌入式键值存储（基于 RocksDB）

use rocksdb::{DB, Options, WriteBatch, IteratorMode};
use serde::{Serialize, Deserialize};
use bincode;
use std::path::Path;

pub struct EmbeddedStore {
    db: DB,
}

impl EmbeddedStore {
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self, rocksdb::Error> {
        let mut opts = Options::default();
        opts.create_if_missing(true);
        opts.set_max_open_files(1000);
        opts.set_write_buffer_size(64 * 1024 * 1024);
        opts.set_max_write_buffer_number(3);
        opts.set_target_file_size_base(64 * 1024 * 1024);

        let db = DB::open(&opts, path)?;
        Ok(Self { db })
    }

    pub fn put<K, V>(&self, key: K, value: &V) -> Result<(), StoreError>
    where
        K: AsRef<[u8]>,
        V: Serialize,
    {
        let encoded = bincode::serialize(value)?;
        self.db.put(key, encoded)?;
        Ok(())
    }

    pub fn get<K, V>(&self, key: K) -> Result<Option<V>, StoreError>
    where
        K: AsRef<[u8]>,
        V: for<'de> Deserialize<'de>,
    {
        match self.db.get(key)? {
            Some(data) => Ok(Some(bincode::deserialize(&data)?)),
            None => Ok(None),
        }
    }

    pub fn delete<K>(&self, key: K) -> Result<(), StoreError>
    where
        K: AsRef<[u8]>,
    {
        self.db.delete(key)?;
        Ok(())
    }

    pub fn batch_write<F>(&self, f: F) -> Result<(), StoreError>
    where
        F: FnOnce(&mut WriteBatch),
    {
        let mut batch = WriteBatch::default();
        f(&mut batch);
        self.db.write(batch)?;
        Ok(())
    }

    pub fn scan_prefix(&self, prefix: &[u8]) -> impl Iterator<Item = (Box<[u8]>, Box<[u8]>)> + '_ {
        self.db.prefix_iterator(prefix)
    }

    pub fn range_scan<K: AsRef<[u8]>>(
        &self,
        start: K,
        end: K,
    ) -> impl Iterator<Item = (Box<[u8]>, Box<[u8]>)> + '_ {
        self.db.iterator(IteratorMode::From(start.as_ref(), rocksdb::Direction::Forward))
            .take_while(move |(k, _)| k.as_ref() < end.as_ref())
    }
}

#[derive(Debug)]
pub enum StoreError {
    RocksDb(rocksdb::Error),
    Serialization(Box<bincode::ErrorKind>),
}

impl From<rocksdb::Error> for StoreError {
    fn from(e: rocksdb::Error) -> Self { Self::RocksDb(e) }
}

impl From<Box<bincode::ErrorKind>> for StoreError {
    fn from(e: Box<bincode::ErrorKind>) -> Self { Self::Serialization(e) }
}
```

### 列式存储引擎

```rust
//! 简化列式存储引擎

use arrow::array::{Array, ArrayRef, Int64Array, Float64Array, StringArray};
use arrow::datatypes::{Schema, Field, DataType};
use arrow::record_batch::RecordBatch;
use std::sync::Arc;
use std::collections::HashMap;

pub struct ColumnStore {
    schema: Arc<Schema>,
    columns: HashMap<String, ArrayRef>,
    row_count: usize,
}

impl ColumnStore {
    pub fn new(schema: Schema) -> Self {
        let schema = Arc::new(schema);
        Self { schema, columns: HashMap::new(), row_count: 0 }
    }

    pub fn from_batch(batch: RecordBatch) -> Self {
        let mut columns = HashMap::new();
        let schema = batch.schema();

        for (i, field) in schema.fields().iter().enumerate() {
            columns.insert(field.name().clone(), batch.column(i).clone());
        }

        Self {
            schema,
            columns,
            row_count: batch.num_rows(),
        }
    }

    pub fn select(&self, columns: &[&str]) -> Result<RecordBatch, String> {
        let selected_fields: Vec<Field> = columns
            .iter()
            .filter_map(|&name| self.schema.field_with_name(name).ok().cloned())
            .collect();

        let selected_arrays: Vec<ArrayRef> = columns
            .iter()
            .filter_map(|&name| self.columns.get(name).cloned())
            .collect();

        let new_schema = Arc::new(Schema::new(selected_fields));
        RecordBatch::try_new(new_schema, selected_arrays)
            .map_err(|e| e.to_string())
    }

    pub fn filter(&self, column: &str, predicate: impl Fn(&dyn Array, usize) -> bool) -> Result<ColumnStore, String> {
        let array = self.columns.get(column).ok_or("Column not found")?;

        let mut indices = Vec::new();
        for i in 0..array.len() {
            if predicate(array.as_ref(), i) {
                indices.push(i);
            }
        }

        // 创建新的列存储，只包含符合条件的行
        let mut new_columns = HashMap::new();
        for (name, col) in &self.columns {
            let filtered = Self::filter_array(col, &indices)?;
            new_columns.insert(name.clone(), filtered);
        }

        Ok(Self {
            schema: self.schema.clone(),
            columns: new_columns,
            row_count: indices.len(),
        })
    }

    fn filter_array(array: &ArrayRef, indices: &[usize]) -> Result<ArrayRef, String> {
        use arrow::compute::take;

        let indices_array = Int64Array::from_iter_values(indices.iter().map(|&i| i as i64));
        take(array, &indices_array, None)
            .map_err(|e| e.to_string())
    }

    pub fn aggregate(&self, group_by: &str, agg_col: &str) -> Result<HashMap<String, f64>, String> {
        let group_array = self.columns.get(group_by).ok_or("Group column not found")?;
        let agg_array = self.columns.get(agg_col).ok_or("Aggregate column not found")?;

        // 简化实现：假设都是字符串和浮点数
        let mut result: HashMap<String, (f64, usize)> = HashMap::new();

        if let (Some(groups), Some(values)) = (
            group_array.as_any().downcast_ref::<StringArray>(),
            agg_array.as_any().downcast_ref::<Float64Array>()
        ) {
            for i in 0..group_array.len() {
                if groups.is_null(i) || values.is_null(i) {
                    continue;
                }
                let group = groups.value(i).to_string();
                let value = values.value(i);

                let entry = result.entry(group).or_insert((0.0, 0));
                entry.0 += value;
                entry.1 += 1;
            }
        }

        Ok(result.into_iter().map(|(k, (sum, count))| (k, sum / count as f64)).collect())
    }

    pub fn to_batch(&self) -> Result<RecordBatch, String> {
        let arrays: Vec<ArrayRef> = self.schema
            .fields()
            .iter()
            .map(|f| self.columns.get(f.name()).cloned())
            .collect::<Option<_>>()
            .ok_or("Missing columns")?;

        RecordBatch::try_new(self.schema.clone(), arrays)
            .map_err(|e| e.to_string())
    }
}
```

---

## 序列化与存储格式

### Apache Arrow

```rust
//! Apache Arrow 数据处理

use arrow::array::{Int64Array, Float64Array, StringArray, ArrayRef};
use arrow::datatypes::{Schema, Field, DataType};
use arrow::record_batch::RecordBatch;
use arrow::ipc::writer::FileWriter;
use arrow::ipc::reader::FileReader;
use std::sync::Arc;

pub struct ArrowProcessor;

impl ArrowProcessor {
    /// 创建示例 RecordBatch
    pub fn create_sample_batch() -> RecordBatch {
        let schema = Arc::new(Schema::new(vec![
            Field::new("id", DataType::Int64, false),
            Field::new("name", DataType::Utf8, false),
            Field::new("value", DataType::Float64, true),
        ]));

        let id_array = Arc::new(Int64Array::from(vec![1, 2, 3, 4, 5])) as ArrayRef;
        let name_array = Arc::new(StringArray::from(vec!["a", "b", "c", "d", "e"])) as ArrayRef;
        let value_array = Arc::new(Float64Array::from(vec![Some(1.0), Some(2.0), None, Some(4.0), Some(5.0)])) as ArrayRef;

        RecordBatch::try_new(schema, vec![id_array, name_array, value_array]).unwrap()
    }

    /// 写入 IPC 格式
    pub fn write_ipc(batch: &RecordBatch, path: &str) -> Result<(), Box<dyn std::error::Error>> {
        let file = std::fs::File::create(path)?;
        let mut writer = FileWriter::try_new(file, batch.schema().as_ref())?;
        writer.write(batch)?;
        writer.finish()?;
        Ok(())
    }

    /// 读取 IPC 格式
    pub fn read_ipc(path: &str) -> Result<Vec<RecordBatch>, Box<dyn std::error::Error>> {
        let file = std::fs::File::open(path)?;
        let reader = FileReader::try_new(file, None)?;
        reader.collect::<Result<Vec<_>, _>>()
            .map_err(|e| e.into())
    }

    /// 列式操作示例
    pub fn column_operations(batch: &RecordBatch) {
        let schema = batch.schema();

        for (i, field) in schema.fields().iter().enumerate() {
            let column = batch.column(i);
            println!("Column {}: {} ({} rows)", field.name(), field.data_type(), column.len());
            println!("  Null count: {}", column.null_count());
            println!("  Memory size: {} bytes", column.get_array_memory_size());
        }
    }
}
```

### Parquet 列式存储

```rust
//! Parquet 列式存储

use parquet::file::properties::WriterProperties;
use parquet::file::writer::SerializedFileWriter;
use parquet::schema::parser::parse_message_type;
use parquet::basic::{Compression, Encoding};
use arrow::array::{ArrayRef, Int64Array, Float64Array, StringArray};
use arrow::record_batch::RecordBatch;
use arrow::datatypes::{Schema, Field, DataType};
use std::sync::Arc;
use std::fs::File;

pub struct ParquetWriter;

impl ParquetWriter {
    /// 写入 Parquet 文件
    pub fn write_batch(batch: &RecordBatch, path: &str) -> Result<(), Box<dyn std::error::Error>> {
        let file = File::create(path)?;

        let props = WriterProperties::builder()
            .set_compression(Compression::SNAPPY)
            .set_encoding(Encoding::PLAIN)
            .build();

        let mut writer = SerializedFileWriter::new(file, batch.schema().clone().into(), Arc::new(props))?;

        // 写入数据
        let mut row_group_writer = writer.next_row_group()?;

        for i in 0..batch.num_columns() {
            let column = batch.column(i);
            // 写入列数据...
        }

        row_group_writer.close()?;
        writer.close()?;

        Ok(())
    }

    /// 使用 Arrow 写入 Parquet
    pub fn write_with_arrow(batch: &RecordBatch, path: &str) -> Result<(), Box<dyn std::error::Error>> {
        let file = File::create(path)?;
        let props = parquet::file::properties::WriterProperties::builder()
            .set_compression(Compression::ZSTD(ZstdLevel::try_new(3)?))
            .build();

        let mut writer = parquet::arrow::ArrowWriter::try_new(file, batch.schema().clone(), Some(props))?;
        writer.write(batch)?;
        writer.close()?;

        Ok(())
    }
}

use parquet::basic::ZstdLevel;
```

---

## ETL 管道

### 完整 ETL 实现

```rust
//! ETL 管道实现

use serde::{Serialize, Deserialize};
use tokio::sync::mpsc;
use std::pin::Pin;
use futures::Stream;

/// ETL 配置
#[derive(Debug, Clone)]
pub struct EtlConfig {
    pub batch_size: usize,
    pub max_concurrency: usize,
    pub error_threshold: f64,
}

impl Default for EtlConfig {
    fn default() -> Self {
        Self {
            batch_size: 1000,
            max_concurrency: 4,
            error_threshold: 0.01,
        }
    }
}

/// ETL 上下文
pub struct EtlContext {
    pub config: EtlConfig,
    pub metrics: EtlMetrics,
}

#[derive(Debug, Default)]
pub struct EtlMetrics {
    pub records_read: u64,
    pub records_written: u64,
    pub records_failed: u64,
    pub bytes_processed: u64,
    pub start_time: Option<std::time::Instant>,
}

/// 数据源 trait
pub trait DataSource<T> {
    fn read(&self) -> Pin<Box<dyn Stream<Item = Result<T, EtlError>> + Send>>;
}

/// 数据目标 trait
pub trait DataSink<T> {
    async fn write(&mut self, records: Vec<T>) -> Result<usize, EtlError>;
    async fn close(&mut self) -> Result<(), EtlError>;
}

/// 转换函数 trait
pub trait Transformer<I, O> {
    fn transform(&self, input: I) -> Result<O, EtlError>;
}

#[derive(Debug)]
pub enum EtlError {
    ReadError(String),
    TransformError(String),
    WriteError(String),
    ValidationError(String),
}

/// ETL 管道
pub struct EtlPipeline<I, O> {
    source: Box<dyn DataSource<I>>,
    transformer: Box<dyn Transformer<I, O>>,
    sink: Box<dyn DataSink<O>>,
    context: EtlContext,
}

impl<I, O> EtlPipeline<I, O>
where
    I: Send + 'static,
    O: Send + 'static,
{
    pub fn new(
        source: Box<dyn DataSource<I>>,
        transformer: Box<dyn Transformer<I, O>>,
        sink: Box<dyn DataSink<O>>,
        config: EtlConfig,
    ) -> Self {
        Self {
            source,
            transformer,
            sink,
            context: EtlContext {
                config,
                metrics: EtlMetrics::default(),
            },
        }
    }

    pub async fn run(mut self) -> Result<EtlMetrics, EtlError> {
        self.context.metrics.start_time = Some(std::time::Instant::now());

        let (tx, mut rx) = mpsc::channel(self.context.config.batch_size);
        let mut stream = self.source.read();

        // 生产者任务：读取并转换数据
        let transform_task = tokio::spawn(async move {
            let mut batch = Vec::with_capacity(self.context.config.batch_size);

            while let Some(result) = stream.next().await {
                match result {
                    Ok(record) => {
                        self.context.metrics.records_read += 1;

                        match self.transformer.transform(record) {
                            Ok(transformed) => {
                                batch.push(transformed);

                                if batch.len() >= self.context.config.batch_size {
                                    if tx.send(batch).await.is_err() {
                                        break;
                                    }
                                    batch = Vec::with_capacity(self.context.config.batch_size);
                                }
                            }
                            Err(e) => {
                                self.context.metrics.records_failed += 1;
                                eprintln!("Transform error: {:?}", e);
                            }
                        }
                    }
                    Err(e) => {
                        self.context.metrics.records_failed += 1;
                        eprintln!("Read error: {:?}", e);
                    }
                }
            }

            // 发送剩余数据
            if !batch.is_empty() {
                let _ = tx.send(batch).await;
            }

            self.context.metrics
        });

        // 消费者任务：写入数据
        while let Some(batch) = rx.recv().await {
            match self.sink.write(batch).await {
                Ok(count) => {
                    self.context.metrics.records_written += count as u64;
                }
                Err(e) => {
                    eprintln!("Write error: {:?}", e);
                }
            }
        }

        self.sink.close().await?;

        let metrics = transform_task.await.unwrap();
        Ok(metrics)
    }
}
```

---

## 实时分析

### 实时指标计算

```rust
//! 实时指标计算引擎

use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use dashmap::DashMap;
use std::time::{SystemTime, UNIX_EPOCH};

/// 滑动窗口指标
pub struct SlidingWindowMetrics {
    window_size_ms: u64,
    buckets: DashMap<u64, MetricsBucket>,
}

struct MetricsBucket {
    count: u64,
    sum: f64,
    sum_squares: f64,
    min: f64,
    max: f64,
}

impl SlidingWindowMetrics {
    pub fn new(window_size_ms: u64) -> Self {
        Self { window_size_ms, buckets: DashMap::new() }
    }

    pub fn record(&self, value: f64) {
        let now = current_time_ms();
        let bucket_key = now / self.window_size_ms;

        self.buckets.entry(bucket_key).and_modify(|b| {
            b.count += 1;
            b.sum += value;
            b.sum_squares += value * value;
            b.min = b.min.min(value);
            b.max = b.max.max(value);
        }).or_insert(MetricsBucket {
            count: 1,
            sum: value,
            sum_squares: value * value,
            min: value,
            max: value,
        });

        // 清理过期桶
        self.cleanup_old_buckets(now);
    }

    pub fn get_stats(&self) -> WindowStats {
        let now = current_time_ms();
        let current_bucket = now / self.window_size_ms;
        let window_start = current_bucket.saturating_sub(10); // 保持10个桶

        let mut total_count = 0u64;
        let mut total_sum = 0.0;
        let mut total_sum_squares = 0.0;
        let mut min = f64::MAX;
        let mut max = f64::MIN;

        for entry in self.buckets.iter() {
            if *entry.key() >= window_start {
                let b = entry.value();
                total_count += b.count;
                total_sum += b.sum;
                total_sum_squares += b.sum_squares;
                min = min.min(b.min);
                max = max.max(b.max);
            }
        }

        let avg = if total_count > 0 { total_sum / total_count as f64 } else { 0.0 };
        let variance = if total_count > 1 {
            (total_sum_squares - (total_sum * total_sum) / total_count as f64) / (total_count - 1) as f64
        } else {
            0.0
        };

        WindowStats {
            count: total_count,
            avg,
            std: variance.sqrt(),
            min: if min == f64::MAX { 0.0 } else { min },
            max: if max == f64::MIN { 0.0 } else { max },
        }
    }

    fn cleanup_old_buckets(&self, now: u64) {
        let cutoff = now / self.window_size_ms - 20;
        self.buckets.retain(|k, _| *k > cutoff);
    }
}

#[derive(Debug, Clone)]
pub struct WindowStats {
    pub count: u64,
    pub avg: f64,
    pub std: f64,
    pub min: f64,
    pub max: f64,
}

fn current_time_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64
}
```

---

## 最佳实践

### 1. 内存管理

```rust
//! 数据工程内存优化

use std::sync::Arc;
use bumpalo::Bump;

/// 使用 arena 分配器处理批量数据
pub fn process_with_arena(data: &[&str]) -> Vec<ProcessedData> {
    let bump = Bump::new();
    let mut results = Vec::new();

    for item in data {
        // 在 arena 中分配字符串，避免大量小堆分配
        let processed = process_item(&bump, item);
        results.push(processed);
    }

    // arena 自动清理所有分配
    results
}

fn process_item<'bump>(bump: &'bump Bump, item: &str) -> ProcessedData<'bump> {
    let stored: &'bump str = bump.alloc_str(item);
    ProcessedData { value: stored }
}

struct ProcessedData<'a> { value: &'a str }
```

### 2. 并发处理

```rust
//! 数据并行处理

use rayon::prelude::*;

pub fn parallel_process<T, F>(data: Vec<T>, f: F) -> Vec<T>
where
    T: Send + Sync,
    F: Fn(&T) -> T + Sync + Send,
{
    data.par_iter().map(f).collect()
}

pub fn parallel_filter<T, F>(data: Vec<T>, predicate: F) -> Vec<T>
where
    T: Send + Sync,
    F: Fn(&T) -> bool + Sync + Send,
{
    data.into_par_iter().filter(predicate).collect()
}
```

### 3. 错误处理

```rust
//! 健壮的错误处理

use thiserror::Error;

#[derive(Error, Debug)]
pub enum DataError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Serialization error: {0}")]
    Serialization(String),

    #[error("Validation error: {field} - {message}")]
    Validation { field: String, message: String },

    #[error("Database error: {0}")]
    Database(String),
}

pub type Result<T> = std::result::Result<T, DataError>;
```

---

## 总结

Rust 在数据工程领域提供了：

1. **极致性能**: 原生性能，无 GC 暂停，适合大规模数据处理
2. **内存效率**: 零拷贝处理，低内存占用
3. **类型安全**: 编译时捕获数据管道错误
4. **并发能力**:  fearless 并发，轻松处理并行数据流
5. **生态成熟**: Polars、DataFusion、Arrow 等世界级数据工具

通过本文档介绍的技术，开发者可以构建高性能、高可靠性的数据处理系统。
