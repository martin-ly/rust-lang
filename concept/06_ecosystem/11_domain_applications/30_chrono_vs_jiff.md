# chrono vs jiff：两代日期时间库的语义分野（实测对照）

> **定位**: `29_time_and_date_ecosystem.md`（chrono 主生态页）的 W4 裁决子页——jiff 是否值得独立 canonical 页的评估结论：**建本页作为选型对比页**，jiff 不单开生态页（其版本实查锚已登记在 29 页 §二）。
> **实测环境**: 本机 rustup toolchain 1.99.1-x86_64-pc-windows-msvc，cargo 1.99.1；依赖 `jiff 0.2.38` / `chrono 0.4.45` / `chrono-tz 0.10.4`（crates.io 2026-10-19 实查最新版）；实测日期 2026-10-19。

---

## 一、核心裁决：jiff 与 chrono 不是同代设计，DST 边界语义直接分叉

同一个「DST 模糊/缺失本地时刻」问题，两库给出**相反的工程姿态**（本机实测，非文档转述）：

| 场景（America/New_York） | chrono 0.4.45 + chrono-tz 0.10.4 实测 | jiff 0.2.38 实测 |
|:---|:---|:---|
| 回拨模糊时刻 2026-11-01 01:30（EDT/EST 各一次） | `LocalResult::Ambiguous(EDT, EST)`——三态显式暴露，调用方被迫处置 | `Ok(2026-11-01T01:30:00-04:00)`——**自动消歧取较早偏移（EDT）**，不报错 |
| 前跳缺失时刻 2026-03-08 02:30（不存在） | `LocalResult::None`——显式「无此时刻」 | `Ok(2026-03-08T03:30:00-04:00)`——**自动平移 +1h 到合法时刻**，不报错 |
| 纯日期串解析为 Timestamp | （chrono 侧 naive 解析默许） | `Timestamp::from_str("2026-10-19")` → **Err**（Timestamp 要求完整 ISO 8601 带偏移/Z，「pit of success」严格入口） |
| 模糊时刻→UTC→回本地往返 | — | `05:30Z → 01:30-04:00 EDT`——往返锁定消歧时选定的偏移，本地 civil 时间不保真回原 ambiguous 的另一解 |

**语义判读**：chrono 的 `LocalResult` 三态把 DST 病态交给调用方（安全但摩擦大，实践中大量代码 `.unwrap()` 或 `.single()` 直接吞掉三态——这是 chrono 生态最大的隐性风险面）；jiff 把消歧策略内置（earlier-offset 消歧模糊时刻、gap-shift 消歧缺失时刻），默认路径不返回错误三态，代价是**消歧决策不可见**——除非主动查询 `TimeZone.offset_at` 或阅读文档约定，调用方不知道自己被代拿了主意。

这不是优劣问题而是**故障暴露位置**的转移：chrono 在「构造点」报，jiff 在「结果偏移」里藏。对定时任务、账单周期、日志对齐这类要求「模糊时刻必须显式二选一」的领域，chrono 的摩擦恰是特性；对解析外部时间戳、追求零样板的 API 层，jiff 的默认消歧恰是价值。

## 二、API 世代差异（选型轴）

- **类型体系**：jiff 是 Temporal 提案的 Rust 投射——`Timestamp`（绝对时刻）/`Zoned`（带时区 civil）/`civil::DateTime`（无时区）三型正交，naive↔aware 转换必须显式过 `TimeZone`；chrono 是 pre-Temporal 世代——`NaiveDateTime`/`DateTime<Tz>`/`LocalResult` 混合，naive 与 aware 的边界靠类型命名约定而非构造强制（29 页 §三不变量在 jiff 里是构造层面的硬约束）。
- **解析严格性**：jiff 默认拒绝缺偏移的 Timestamp 输入（实测 §一表行 3）；chrono 对 naive 串一路默许。jiff 的 Err 是 `Error` 单类型全路径传播，chrono 的失败散在 `ParseError`/`LocalResult::None`/`.unwrap()` panic 三处。
- **时区数据**：chrono 靠 chrono-tz 编译期嵌入 IANA 表（`Tz` 枚举，`filter-by-regex` 可裁剪）；jiff 可选 `jiff-tzdb`（实测依赖树含 `jiff-tzdb 0.1.9`）、`tz-fat`（完整含历史规则）、或系统 tz（Windows 走 C++/icu 路径）。29 页 chrono-tz 三态实测与本页 jiff 消歧实测构成互补证据对。
- **版本势头**（crates.io 2026-10-19 实查，29 页 §二已录）：jiff 0.2.38 近期下载 ~8,789 万 vs chrono 0.4.45 同期 ~1.8 亿量级——jiff 已达 chrono 半量级且 0.2 线 70 版本高频迭代；jiff 作者 BurntSushi 即 ripgrep 作者，维护可信度一级。

## 三、选型判据（决策树）

1. 依赖既有 chrono 代码库、只需修时间戳边界 bug → **留在 chrono**，按 29 页 §五清单加 `checked_sub`/`LocalResult` 显式处置；迁 jiff 的重写成本 > 收益（NexusTrade 一手复盘的教训：重写收益在性能与类型面，不在 DST 语义）。
2. 新项目、外部输入时间戳解析占比高、无 naive 需求 → **jiff**：严格入口把 chrono 生态的隐性 `.unwrap()` 风险直接编译期/解析期消灭。
3. 模糊/缺失时刻必须显式处置（调度、结算、合规窗口） → 两库皆可但姿势不同：chrono 天然强制、jiff 需主动 `TimeZone.offset_at` + 文档化消歧约定（jiff 提供 `OffsetConflict` 选项可把默认消歧改回显式报错——把 jiff 拉回 chrono 式纪律）。
4. no_std/wasm → jiff 原生双 category（`date-and-time + no-std`）；chrono 侧 29 页已录时间组件方案。

## 四、来源与证据索引

- 本机实测（P0 级，可复现）：cargo 1.99.1 + jiff 0.2.38/chrono 0.4.45/chrono-tz 0.10.4 对照程序（§一表四行全部来自同一二进制 stdout）。
- [jiff docs.rs 0.2.38](https://docs.rs/jiff/0.2.38/jiff/tz/struct.TimeZone.html)（P0：0.2.38 版本页、依赖树含 jiff-tzdb 0.1.9、dev-deps 含 chrono/chrono-tz/time——作者自设跨库对照测试面）。
- [BurntSushi/jiff](https://github.com/BurntSushi/jiff)（P0：「pit of success」设计宣言与消歧策略文档）。
- [chrono-tz docs](https://docs.rs/chrono-tz)（P1：LocalResult 三态语义）。
- crates.io API 版本/下载实查（P0，2026-10-19）：jiff 0.2.38（2026-10-06）· jiff-tzdb 0.1.9 · chrono 0.4.45 · chrono-tz 0.10.4。
- 交叉页：`29_time_and_date_ecosystem.md`（chrono 主生态、jiff 版本实查锚、chrono-tz 三态实测）。
