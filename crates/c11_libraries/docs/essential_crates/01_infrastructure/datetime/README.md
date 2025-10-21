# 时间与日期处理

> **核心库**: chrono, time  
> **适用场景**: 时间戳、日期计算、时区转换、格式化

---

## 📋 目录

- [时间与日期处理](#时间与日期处理)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [时间相关术语](#时间相关术语)
    - [时间处理挑战](#时间处理挑战)
  - [🦀 chrono 库](#-chrono-库)
    - [特点](#特点)
    - [基础用法](#基础用法)
      - [获取当前时间](#获取当前时间)
      - [解析和格式化](#解析和格式化)
      - [时间计算](#时间计算)
      - [时区转换](#时区转换)
    - [高级特性](#高级特性)
      - [Serde 集成](#serde-集成)
      - [周期性任务](#周期性任务)
  - [⏰ time 库](#-time-库)
    - [特点1](#特点1)
    - [基础用法1](#基础用法1)
    - [高精度时间](#高精度时间)
  - [🎯 库选择指南](#-库选择指南)
    - [对比矩阵](#对比矩阵)
    - [推荐使用场景](#推荐使用场景)
  - [💡 最佳实践](#-最佳实践)
    - [1. 始终使用 UTC 存储](#1-始终使用-utc-存储)
      - [✅ 推荐](#-推荐)
      - [❌ 避免](#-避免)
    - [2. 处理用户输入](#2-处理用户输入)
    - [3. 数据库存储](#3-数据库存储)
    - [4. API 响应格式](#4-api-响应格式)
  - [🔧 常见场景](#-常见场景)
    - [场景 1: 计算年龄](#场景-1-计算年龄)
    - [场景 2: 营业时间判断](#场景-2-营业时间判断)
    - [场景 3: 到期时间检查](#场景-3-到期时间检查)
    - [场景 4: 时间范围查询](#场景-4-时间范围查询)
  - [📚 延伸阅读](#-延伸阅读)

---

## 🎯 核心概念

### 时间相关术语

| 术语 | 说明 | 示例 |
|------|------|------|
| **Timestamp** | Unix 时间戳 | 1729468800 |
| **DateTime** | 日期+时间 | 2025-10-20 15:30:00 |
| **Date** | 仅日期 | 2025-10-20 |
| **Time** | 仅时间 | 15:30:00 |
| **Duration** | 时间间隔 | 3 hours |
| **Timezone** | 时区 | UTC, UTC+8 |
| **Offset** | 时区偏移 | +08:00 |

### 时间处理挑战

1. **时区处理**: UTC vs Local vs 其他时区
2. **夏令时**: 时间跳跃和重叠
3. **闰秒**: 偶尔的额外秒
4. **精度**: 秒、毫秒、微秒、纳秒
5. **序列化**: 如何存储和传输

---

## 🦀 chrono 库

### 特点

- ✅ **功能全面**: 完整的日期时间操作
- ✅ **时区支持**: 基于 IANA 时区数据库
- ✅ **易用性**: API 直观友好
- ❌ **依赖较重**: 包含时区数据
- ❌ **性能一般**: 相比 time 稍慢

### 基础用法

#### 获取当前时间

```rust
use chrono::{DateTime, Utc, Local, FixedOffset};

fn main() {
    // UTC 时间
    let utc_now: DateTime<Utc> = Utc::now();
    println!("UTC: {}", utc_now);
    
    // 本地时间
    let local_now: DateTime<Local> = Local::now();
    println!("Local: {}", local_now);
    
    // 固定偏移时区 (UTC+8)
    let offset = FixedOffset::east_opt(8 * 3600).unwrap();
    let cn_now = DateTime::<Utc>::from(utc_now).with_timezone(&offset);
    println!("CN: {}", cn_now);
}
```

#### 解析和格式化

```rust
use chrono::{DateTime, Utc, NaiveDate};

fn main() -> Result<(), chrono::ParseError> {
    // 解析 ISO 8601
    let dt = "2025-10-20T15:30:00Z".parse::<DateTime<Utc>>()?;
    println!("Parsed: {}", dt);
    
    // 解析自定义格式
    let date = NaiveDate::parse_from_str("2025-10-20", "%Y-%m-%d")?;
    println!("Date: {}", date);
    
    // 格式化输出
    println!("Format 1: {}", dt.format("%Y-%m-%d %H:%M:%S"));
    println!("Format 2: {}", dt.format("%Y年%m月%d日"));
    println!("RFC2822: {}", dt.to_rfc2822());
    println!("RFC3339: {}", dt.to_rfc3339());
    
    Ok(())
}
```

#### 时间计算

```rust
use chrono::{DateTime, Utc, Duration};

fn main() {
    let now = Utc::now();
    
    // 加减时间
    let tomorrow = now + Duration::days(1);
    let yesterday = now - Duration::days(1);
    let later = now + Duration::hours(3) + Duration::minutes(30);
    
    println!("Now: {}", now);
    println!("Tomorrow: {}", tomorrow);
    println!("Later: {}", later);
    
    // 计算时间差
    let diff = tomorrow - now;
    println!("Difference: {} seconds", diff.num_seconds());
    println!("Difference: {} hours", diff.num_hours());
}
```

#### 时区转换

```rust
use chrono::{DateTime, Utc, FixedOffset, TimeZone};

fn main() {
    let utc_time = Utc::now();
    println!("UTC: {}", utc_time);
    
    // 转换到东八区
    let beijing_offset = FixedOffset::east_opt(8 * 3600).unwrap();
    let beijing_time = utc_time.with_timezone(&beijing_offset);
    println!("Beijing: {}", beijing_time);
    
    // 转换到西五区
    let ny_offset = FixedOffset::west_opt(5 * 3600).unwrap();
    let ny_time = utc_time.with_timezone(&ny_offset);
    println!("New York: {}", ny_time);
}
```

### 高级特性

#### Serde 集成

```rust
use chrono::{DateTime, Utc};
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug)]
struct Event {
    name: String,
    
    // 自动序列化为 RFC3339 字符串
    #[serde(with = "chrono::serde::ts_seconds")]
    timestamp: DateTime<Utc>,
    
    // 可选的自定义格式
    #[serde(
        serialize_with = "serialize_custom",
        deserialize_with = "deserialize_custom"
    )]
    created_at: DateTime<Utc>,
}

fn serialize_custom<S>(dt: &DateTime<Utc>, s: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    let formatted = dt.format("%Y-%m-%d %H:%M:%S").to_string();
    s.serialize_str(&formatted)
}

fn deserialize_custom<'de, D>(d: D) -> Result<DateTime<Utc>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let s = String::deserialize(d)?;
    DateTime::parse_from_rfc3339(&s)
        .map(|dt| dt.with_timezone(&Utc))
        .map_err(serde::de::Error::custom)
}
```

#### 周期性任务

```rust
use chrono::{DateTime, Utc, Duration, Datelike};

struct ScheduledTask {
    next_run: DateTime<Utc>,
    interval: Duration,
}

impl ScheduledTask {
    fn new(interval: Duration) -> Self {
        Self {
            next_run: Utc::now() + interval,
            interval,
        }
    }
    
    fn should_run(&self) -> bool {
        Utc::now() >= self.next_run
    }
    
    fn update_next_run(&mut self) {
        self.next_run = self.next_run + self.interval;
    }
}

// 每月第一天执行
fn is_first_day_of_month(dt: &DateTime<Utc>) -> bool {
    dt.day() == 1
}
```

---

## ⏰ time 库

### 特点1

- ✅ **高性能**: 零成本抽象
- ✅ **轻量级**: 最小依赖
- ✅ **类型安全**: 强类型设计
- ✅ **现代化**: 更好的API设计
- ❌ **学习曲线**: 相对陡峭

### 基础用法1

```rust
use time::{OffsetDateTime, Duration, format_description};

fn main() -> Result<(), time::Error> {
    // 当前时间
    let now = OffsetDateTime::now_utc();
    println!("Now: {}", now);
    
    // 时间计算
    let tomorrow = now + Duration::days(1);
    let next_week = now + Duration::weeks(1);
    
    // 格式化
    let format = format_description::parse("[year]-[month]-[day] [hour]:[minute]:[second]")?;
    println!("Custom: {}", now.format(&format)?);
    
    Ok(())
}
```

### 高精度时间

```rust
use time::{OffsetDateTime, Duration};

fn benchmark<F>(f: F) -> Duration
where
    F: FnOnce(),
{
    let start = OffsetDateTime::now_utc();
    f();
    let end = OffsetDateTime::now_utc();
    end - start
}

fn main() {
    let duration = benchmark(|| {
        // 执行一些操作
        for _ in 0..1000 {
            let _ = vec![1, 2, 3];
        }
    });
    
    println!("Took: {} microseconds", duration.whole_microseconds());
}
```

---

## 🎯 库选择指南

### 对比矩阵

| 特性 | chrono | time | 推荐场景 |
|------|--------|------|----------|
| **易用性** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | chrono |
| **性能** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | time |
| **时区支持** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | chrono |
| **依赖大小** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | time |
| **API 稳定性** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | chrono |
| **类型安全** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | time |

### 推荐使用场景

**选择 chrono**:

- ✅ 通用 Web 应用
- ✅ 需要复杂时区处理
- ✅ 快速开发原型
- ✅ 与现有 chrono 代码集成

**选择 time**:

- ✅ 高性能要求
- ✅ 嵌入式系统
- ✅ 最小化依赖
- ✅ 需要最新的类型安全特性

---

## 💡 最佳实践

### 1. 始终使用 UTC 存储

#### ✅ 推荐

```rust
use chrono::{DateTime, Utc, FixedOffset};

#[derive(Debug)]
struct User {
    id: u64,
    created_at: DateTime<Utc>, // 存储 UTC
}

fn display_user_time(user: &User, user_timezone_offset: i32) {
    let offset = FixedOffset::east_opt(user_timezone_offset * 3600).unwrap();
    let local_time = user.created_at.with_timezone(&offset);
    println!("Created at (local): {}", local_time);
}
```

#### ❌ 避免

```rust
// 不要存储本地时间！
struct User {
    created_at: DateTime<Local>, // 时区信息丢失！
}
```

### 2. 处理用户输入

```rust
use chrono::{DateTime, Utc, NaiveDateTime};

fn parse_user_date(input: &str) -> Result<DateTime<Utc>, chrono::ParseError> {
    // 尝试多种格式
    if let Ok(dt) = input.parse::<DateTime<Utc>>() {
        return Ok(dt);
    }
    
    if let Ok(naive) = NaiveDateTime::parse_from_str(input, "%Y-%m-%d %H:%M:%S") {
        return Ok(DateTime::from_naive_utc_and_offset(naive, Utc));
    }
    
    // 其他格式...
    Err(chrono::ParseError(chrono::ParseErrorKind::Invalid))
}
```

### 3. 数据库存储

```rust
use chrono::{DateTime, Utc};

// PostgreSQL
fn store_timestamp(dt: DateTime<Utc>) -> i64 {
    dt.timestamp() // Unix 时间戳（秒）
}

// 高精度存储（微秒）
fn store_timestamp_micros(dt: DateTime<Utc>) -> i64 {
    dt.timestamp_micros()
}

// 从数据库读取
fn load_timestamp(timestamp: i64) -> Option<DateTime<Utc>> {
    DateTime::from_timestamp(timestamp, 0)
}
```

### 4. API 响应格式

```rust
use chrono::{DateTime, Utc};
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct ApiResponse {
    // ISO 8601 / RFC 3339 格式
    timestamp: DateTime<Utc>,
    
    // 或者使用 Unix 时间戳
    #[serde(with = "chrono::serde::ts_seconds")]
    created_at: DateTime<Utc>,
}

fn main() {
    let response = ApiResponse {
        timestamp: Utc::now(),
        created_at: Utc::now(),
    };
    
    let json = serde_json::to_string_pretty(&response).unwrap();
    println!("{}", json);
    // {
    //   "timestamp": "2025-10-20T15:30:00Z",
    //   "created_at": 1729468800
    // }
}
```

---

## 🔧 常见场景

### 场景 1: 计算年龄

```rust
use chrono::{Datelike, Utc};

fn calculate_age(birth_date: chrono::NaiveDate) -> u32 {
    let today = Utc::now().date_naive();
    let mut age = today.year() - birth_date.year();
    
    if today.month() < birth_date.month() ||
       (today.month() == birth_date.month() && today.day() < birth_date.day()) {
        age -= 1;
    }
    
    age as u32
}

fn main() {
    use chrono::NaiveDate;
    let birth = NaiveDate::from_ymd_opt(1990, 5, 15).unwrap();
    println!("Age: {}", calculate_age(birth));
}
```

### 场景 2: 营业时间判断

```rust
use chrono::{Timelike, Utc, Weekday};

fn is_business_hours() -> bool {
    let now = Utc::now();
    
    // 周一到周五
    match now.weekday() {
        Weekday::Sat | Weekday::Sun => return false,
        _ => {}
    }
    
    // 9:00 - 18:00
    let hour = now.hour();
    hour >= 9 && hour < 18
}
```

### 场景 3: 到期时间检查

```rust
use chrono::{DateTime, Utc, Duration};

struct Subscription {
    expires_at: DateTime<Utc>,
}

impl Subscription {
    fn is_expired(&self) -> bool {
        Utc::now() > self.expires_at
    }
    
    fn days_until_expiry(&self) -> i64 {
        (self.expires_at - Utc::now()).num_days()
    }
    
    fn is_expiring_soon(&self) -> bool {
        self.days_until_expiry() <= 7 && !self.is_expired()
    }
}
```

### 场景 4: 时间范围查询

```rust
use chrono::{DateTime, Utc, Duration};

fn get_last_7_days() -> (DateTime<Utc>, DateTime<Utc>) {
    let end = Utc::now();
    let start = end - Duration::days(7);
    (start, end)
}

fn get_current_month() -> (DateTime<Utc>, DateTime<Utc>) {
    let now = Utc::now();
    let start = now
        .with_day(1).unwrap()
        .with_hour(0).unwrap()
        .with_minute(0).unwrap()
        .with_second(0).unwrap();
    let end = now;
    (start, end)
}
```

---

## 📚 延伸阅读

- [chrono 官方文档](https://docs.rs/chrono/)
- [time 官方文档](https://docs.rs/time/)
- [时区数据库 (IANA)](https://www.iana.org/time-zones)

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
