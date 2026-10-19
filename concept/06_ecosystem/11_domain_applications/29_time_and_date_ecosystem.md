# Rust 日期与时间生态（chrono 系）

> **EN**: Time & Date Ecosystem in Rust (chrono family)
> **Bloom 层级**: L3-L5
> **Summary**: crates.io `date-and-time` 分类（935 crates）的 canonical 生态页：std `Instant`/`SystemTime` 边界、chrono 0.4.45 类型体系、chrono-tz 0.10.4 IANA 语义（中国 DST 历史、歧义/跳表三态）、time 0.3.55 对比与 2038/单调钟工程边界。本页补齐对称差报告登记的「54 页顺带提及、0 专页」缺口（2026-10-19）。
> **受众**: [入门→进阶]
> **内容分级**: [综述级+实测]
> **前置概念**: [标准库时间原语](../../04_formal/09_system_semantics) · [系统语言时间处理对比（L5）](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
> **关联**: [可观测性与 SRE 模式](../14_enterprise_architecture/09_observability_and_sre_patterns.md)

---

## 一、std 边界：标准库有意不提供时区

`std::time::Instant`（单调钟，仅用于测速间隔，可在进程间任意起点）与 `std::time::SystemTime`（挂钟，可 `duration_since(UNIX_EPOCH)`，可前于 epoch 返回 `Err`）是 std 的全部时间原语。**Rust 标准库无 Date、无时区、无格式化**——这是设计决策（RFC 时期反复讨论后刻意推迟），因此生态库填补该真空，此即 chrono 长期占据 crates.io 时间类事实标准的根本原因。

## 二、生态版本实查（crates.io API，2026-10-19）

| crate | 当前 stable | 下载量（累计/近期） | 定位 |
|---|---|---|---|
| chrono | **0.4.45**（2026-06-04 发布） | 7.77 亿 / 1.66 亿 | date-and-time 分类事实标准，https://github.com/chronotope/chrono |
| time | **0.3.55**（2026-08-01 发布） | 8.64 亿 / 1.65 亿 | no-std+date-and-time+value-formatting+parser-implementations 四分类，proc-macro 编译期格式化 |
| chrono-tz | **0.10.4** | 1.45 亿 / 3,189 万 | IANA tz 数据库编译进 crate（76,849 行代码生成物，MSRV 1.65） |

本机实测佐证：`cargo add chrono chrono-tz` 在 rustc 1.99.1 下解析锁定 `chrono = 0.4.45` / `chrono-tz = 0.10.4`（Cargo.lock 实测，2026-10-19）。

chrono 依赖链历史包袱（`why-chrono` 议题，chrono#426 系）：依赖 `num-traits`、`iana-time-zone`；0.4.x 线长期保持 API 演化谨慎。time crate 以「fully interoperable with std」为卖点且核心 no-std，嵌入式时间处理优先评估 time 而非 chrono。

## 三、chrono 类型体系核心不变量：naive ≠ aware

`NaiveDate`/`NaiveTime`/`NaiveDateTime` 无时区语义；`DateTime<Tz>`/`DateTime<FixedOffset>` 带 offset。类型系统禁止二者隐式混合——**类型即文档**，这是 chrono 相对 C `time_t` 混用传统的核心工程价值。

```rust,compile_fail
use chrono::{NaiveDate, Utc};
fn main() {
    let nd1 = NaiveDate::from_ymd_opt(2026, 10, 19).unwrap();
    let nd2 = NaiveDate::from_ymd_opt(2026, 10, 26).unwrap();
    let _ = nd1 + nd2; // E0277: 两个日期不能相加; NaiveDate 只可加 TimeDelta/Months/Days
}
```

```rust,compile_fail
use chrono::{NaiveDate, Utc};
fn main() {
    let nd = NaiveDate::from_ymd_opt(2026, 10, 19).unwrap();
    let now = Utc::now();
    let mixed = nd.and_hms_opt(0, 0, 0).unwrap() + now; // E0277: NaiveDateTime + DateTime<Utc> 无实现
    println!("{:?}", mixed);
}
```

对照可编译正例（chrono 0.4.45，本机 cargo 实测通过）：

```rust
use chrono::{NaiveDate, TimeDelta, Utc};
fn main() {
    let nd = NaiveDate::from_ymd_opt(2026, 10, 19).unwrap();
    let later = nd + TimeDelta::days(7); // naive + delta 合法
    let aware = Utc::now();
    println!("{} / aware offset={}", later, aware.offset());
}
```

本机 rustc 1.99.1 (58cf8f9c3 2026-10-13) + `--extern chrono=libchrono(0.4.45)` 全编译实测（EXIT 1），两条 E0277 原文要点：

```text
error[E0277]: cannot add `NaiveDate` to `NaiveDate`
  = help: the trait `Add` is not implemented for `NaiveDate`
  (impl 清单: Add<TimeDelta> / Add<Months> / Add<Days>)
error[E0277]: cannot add `DateTime<Utc>` to `NaiveDateTime`
  = help: the trait `Add<DateTime<Utc>>` is not implemented for `NaiveDateTime`
  (impl 清单: Add<Days>/Add<Duration>/Add<FixedOffset>/Add<Months>/Add<TimeDelta>)
error: aborting due to 2 previous errors
```

注意chrono API 演化史实（本机实测）：`TimeZone::ymd().and_hms_opt()` 老链已移除（E0599 提示「use `with_ymd_and_hms()` instead」）；`TzOffset::to_fixed_offset()` 亦非现行路径，现行经 `chrono::Offset` trait 的 `fix().local_minus_utc()`。历史教程按老 API 抄写会编译失败——版本实查锚的意义即在此。

## 四、chrono-tz 实测：IANA 语义三态 LocalResult

`with_ymd_and_hms` 返回 `LocalResult`：`Single`（唯一解）/ `Ambiguous`（fall-back 重复小时，给出前后两个 offset）/ `None`（spring-forward 跳表，本地时间不存在）。rustc 1.99.1 + chrono-tz 0.10.4 本机实测（cargo run，EXIT 0）：

```text
Asia/Shanghai now offset=28800 abbr=CST
1987-05-10 12:00 Asia/Shanghai -> Single offset=32400 abbr=CDT
2026-07-01 00:00 Asia/Shanghai -> Single offset=28800 abbr=CST
NY 2026-11-01 01:30 (fall-back) -> Ambiguous: -14400(EDT) / -18000(EST)
NY 2026-03-08 02:30 (spring-forward) -> None (本地时间不存在, 春季跳表)
naive=2026-10-19 weekday=Mon
```

三点权威对齐结论：

1. **中国夏令时是历史事实而非现行规则**：1987-05-10 上海解析为 `CDT +09:00`（IANA 快照保留 1986–1991 中国 DST 记录，本机实测），2026 全年恒 `CST +08:00`。中文业务系统若按「中国无夏令时」的直觉写死 +08:00，处理 1986–1991 历史数据（金融回测、档案时间）会产生一小时系统性偏差——chrono-tz 的 IANA 数据库是唯一免维护对策。
2. **fall-back 歧义必须由业务层裁决**：NY 01:30 两次出现，chrono 不猜，返回 Ambiguous 双 offset——与 PostgreSQL `timestamp with time zone` 的显式 offset 策略、以及 `DateTime::from_local` 类隐式取先解的库行为形成对照。
3. **spring-forward 生成不存在的本地时间**：`None` 分支必须显式处理，否则 `unwrap()` 运行时 panic——日期计算器/排班系统的高频线上事故源。

## 五、工程边界与常见误用（分析性，标注来源类型）

- **`Instant` 不可跨进程持久化**：单调钟无绝对原点，把 Instant 读数存库比对是典型错误（应存 SystemTime 或 DateTime）。
- **SystemTime→UNIX epoch 转换的 2038 语义**：`SystemTime` 内部按有符号秒+纳秒建模，平台相关边界（Windows 与 Unix 系实现不同）；长期系统存 `i64` 纳秒/毫秒 epoch 是生态惯例（chrono 默认 i64 年份可达范围远大于 2038）。
- **`Local::now()` 依赖 OS tz 环境**（chrono iana-time-zone 后端：Unix 读 `/etc/localtime`，Windows 走 FFI）——容器镜像缺 tzdata 时 UTC 退化，部署侧应显式设 `TZ` 或用 chrono-tz 显式 `Tz`（P2 级运维共识，登记为分析性断言）。
- **serde 序列化默认 RFC 3339**：`chrono` 的 serde feature 走 `RFC3339` 严格格式，与业务侧常见的无 offset 格式互操作需显式 `with` 适配器（chrono 文档 docs.rs/chrono 口径）。

## 六、canonical 缺口登记（五要素④）

- 库内此前 54 页顺带提及 chrono 而 0 专页 → 本页为 canonical 填补（对称差 T1 条目 `date-and-time(935)` 已闭环）。
- **jiff（crates.io 实查 2026-10-19）**：**0.2.38**（2026-10-06 发布，0.2 线 70 个版本），累计 **2.32 亿** / 近期 **8,789 万** 下载，BurntSushi（Andrew Gallant）维护，categories = `date-and-time + no-std`，Temporal 风格 API（"jump into the pit of success"），特性体系含 `tz-system/tz-fat/static-tz/wasm-bindgen(js)`。近期下载已达 chrono 同期量级的一半，是 date-and-time 分类 2025-2026 最强上升者；chrono vs jiff 选型对比页 W4 裁决：**已建** `30_chrono_vs_jiff.md`（本机 cargo 1.99.1 实测对照：DST 模糊/缺失时刻两库姿态相反）。
- `aws-iot-device-sdk` 实查：0.0.6（2022-09 最后更新，累计 8,944 下载，标注 unofficial）——印证 D3 登记的「IoT SDK 无 canonical crate」为**生态事实**而非库内缺口。
- 未来候选子页：日历/业务时间（workday-calc 类 crate 实查待轮）。

## 七、权威来源索引（P0/P1/P2）

- P0: https://crates.io/api/v1/crates/chrono · https://crates.io/api/v1/crates/chrono-tz · https://crates.io/api/v1/crates/time （2026-10-19 API 实查，版本/下载量口径）
- P0: https://github.com/chronotope/chrono · https://github.com/chronotope/chrono-tz · https://github.com/time-rs/time
- P0: https://doc.rust-lang.org/std/time/index.html （std 时间原语边界——`Instant`/`SystemTime` 为 std 全部时间能力，chrono 真空填补论断的官方依据，2026-10-19 核验）
- P0: 本机 rustc 1.99.1 + cargo 1.99.1 实测记录（Cargo.lock + cargo run + rustc --extern，2026-10-19）
- P1: https://docs.rs/chrono/latest/chrono/ · IANA tz database https://www.iana.org/time-zones （中国 DST 1986–1991 记录）
- P1 学术锚（2026-10-20 arXiv API 实核）: [Pitfalls and Guidelines for Using Time-Based Git Data (Flint, Chauhan, Dyer)](https://arxiv.org/abs/2209.04511)（2022-09-09 提交）——基于时间戳的开源数据研究中时区/时钟陷阱的实证指南，佐证本页「时间处理是全生态系统性 bug 温床」判读口径（口径限于 Git 时间数据取证，Rust 时间库结论仍以本页 crates.io 实查为准）。
- P2: chrono GitHub issue #426（依赖负担议题，历史讨论）
