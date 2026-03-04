# Chrono 时间处理形式化分析

> **主题**: 类型安全的日期时间处理
>
> **形式化框架**: 时间类型系统 + 时区转换
>
> **参考**: Chrono Documentation; ISO 8601 Standard

---

## 目录

- [Chrono 时间处理形式化分析](#chrono-时间处理形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 时间类型层次](#2-时间类型层次)
    - [2.1 NaiveDateTime vs DateTime](#21-naivedatetime-vs-datetime)
    - [定义 2.1 (时间类型)](#定义-21-时间类型)
    - [定理 2.1 (类型区分)](#定理-21-类型区分)
    - [2.2 类型安全边界](#22-类型安全边界)
    - [定理 2.2 (无效日期编译时排除)](#定理-22-无效日期编译时排除)
  - [3. 时区处理](#3-时区处理)
    - [3.1 固定偏移 vs 动态时区](#31-固定偏移-vs-动态时区)
    - [定理 3.1 (时区转换)](#定理-31-时区转换)
    - [3.2 夏令时处理](#32-夏令时处理)
    - [定理 3.2 (夏令时不明确时间)](#定理-32-夏令时不明确时间)
  - [4. 解析与格式化](#4-解析与格式化)
    - [4.1 编译时格式检查](#41-编译时格式检查)
    - [定理 4.1 (格式字符串)](#定理-41-格式字符串)
    - [4.2 解析错误处理](#42-解析错误处理)
    - [定理 4.2 (解析结果)](#定理-42-解析结果)
  - [5. 持续时间与区间](#5-持续时间与区间)
    - [定理 5.1 (Duration算术)](#定理-51-duration算术)
  - [6. 反例与常见错误](#6-反例与常见错误)
    - [反例 6.1 (混用无时区和有时区)](#反例-61-混用无时区和有时区)
    - [反例 6.2 (忽略时区转换)](#反例-62-忽略时区转换)
    - [反例 6.3 (Duration月份)](#反例-63-duration月份)
  - [参考文献](#参考文献)

---

## 1. 引言

Chrono提供:

- **类型安全**: 区分无时区和有时区时间
- **时区支持**: IANA时区数据库
- **格式化**: strftime/strptime
- **持续时间**: 精确时间计算

---

## 2. 时间类型层次

### 2.1 NaiveDateTime vs DateTime

### 定义 2.1 (时间类型)

```rust
// 无时区概念
pub struct NaiveDateTime {
    date: NaiveDate,
    time: NaiveTime,
}

// 有时区
pub struct DateTime<Tz: TimeZone> {
    datetime: NaiveDateTime,
    offset: Tz::Offset,
}
```

### 定理 2.1 (类型区分)

> NaiveDateTime和DateTime不能隐式转换。

**证明**:

```rust
let naive: NaiveDateTime = Local::now().naive_local();
// let dt: DateTime<Utc> = naive;  // 编译错误!

// 必须显式指定时区
let dt: DateTime<Utc> = DateTime::from_utc(naive, Utc);
```

**语义**:

- `NaiveDateTime`: 本地时间，无偏移信息
- `DateTime<Tz>`: 绝对时间点

∎

### 2.2 类型安全边界

### 定理 2.2 (无效日期编译时排除)

> 无效日期在编译时或运行时早期捕获。

**证明**:

```rust
// 编译错误: 越界
let date = NaiveDate::from_ymd_opt(2024, 13, 1);  // None

// 运行时检查
let date = NaiveDate::from_ymd_opt(2024, 2, 30);  // None (2月无30日)
```

∎

---

## 3. 时区处理

### 3.1 固定偏移 vs 动态时区

| 类型 | 说明 | 用途 |
|------|------|------|
| `FixedOffset` | 固定偏移(如+09:00) | 简单偏移 |
| `Utc` | 零偏移 | 存储/计算 |
| `Local` | 系统时区 | 显示 |
| `Tz::IANA` | IANA数据库 | 精确时区 |

### 定理 3.1 (时区转换)

> DateTime可以在时区间转换，保持绝对时间。

**证明**:

```rust
let dt_utc: DateTime<Utc> = Utc::now();
let dt_shanghai: DateTime<Tz> = dt_utc.with_timezone(&Shanghai);
let dt_local: DateTime<Local> = dt_utc.with_timezone(&Local);

// 表示同一绝对时间点
assert_eq!(dt_utc.timestamp(), dt_shanghai.timestamp());
```

∎

### 3.2 夏令时处理

### 定理 3.2 (夏令时不明确时间)

> 夏令时转换期间的时间可能无效或 ambiguous。

**处理**:

```rust
// 重叠时间(回退)
let ambiguous = Shanghai.ymd_opt(2024, 11, 3)
    .and_hms_opt(1, 30, 0);  // 可能返回 Ambiguous

// 跳过时间(前进)
let skipped = Shanghai.ymd_opt(2024, 3, 10)
    .and_hms_opt(2, 30, 0);  // 可能返回 None
```

∎

---

## 4. 解析与格式化

### 4.1 编译时格式检查

### 定理 4.1 (格式字符串)

> format!宏编译时检查格式字符串。

**示例**:

```rust
let dt = Local::now();
let s = dt.format("%Y-%m-%d %H:%M:%S").to_string();
```

**说明符**:

- `%Y`: 四位年份
- `%m`: 月份(01-12)
- `%d`: 日期(01-31)
- `%H`: 小时(00-23)

∎

### 4.2 解析错误处理

### 定理 4.2 (解析结果)

> 解析可能失败，返回Result。

**实现**:

```rust
let dt = NaiveDateTime::parse_from_str(
    "2024-03-15 14:30:00",
    "%Y-%m-%d %H:%M:%S"
)?;
```

∎

---

## 5. 持续时间与区间

### 定理 5.1 (Duration算术)

> Duration支持安全的时间加减。

**实现**:

```rust
let dt = Utc::now();
let tomorrow = dt + Duration::days(1);
let yesterday = dt - Duration::days(1);
```

**注意**: 由于leap second的存在，Duration::seconds(86400) 不一定等于 Duration::days(1)。

∎

---

## 6. 反例与常见错误

### 反例 6.1 (混用无时区和有时区)

```rust
let local = Local::now();
let utc = Utc::now();

// 错误: 直接比较
// if local == utc { ... }  // 编译错误! 类型不同

// 正确: 都转换为timestamp
if local.timestamp() == utc.timestamp() { ... }
```

### 反例 6.2 (忽略时区转换)

```rust
// 存储无时区时间，丢失信息
let naive = Local::now().naive_local();
store_in_db(naive);

// 之后无法确定原始时区

// 正确: 存储UTC
let utc = Local::now().with_timezone(&Utc);
store_in_db(utc);
```

### 反例 6.3 (Duration月份)

```rust
// 错误: 没有标准"月份"持续时间
let next_month = now + Duration::days(30);  // 不准确!

// 正确: 使用月份算术
let next_month = now.checked_add_months(chrono::Months::new(1));
```

---

## 参考文献

1. **Chrono Contributors.** (2024). *Chrono Documentation*. <https://docs.rs/chrono/>

2. **ISO.** (2019). *ISO 8601:2019 Data elements and interchange formats*.

---

*文档版本: 1.0.0*
*形式化深度: 高*
*定理数量: 7个*
*最后更新: 2026-03-04*
