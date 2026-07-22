# 国际化权威来源 URL 健康（2026-07-23）

**EN**: International Authority URL Health
**Summary**: 仅检查 P0/P1/P2 权威域 URL 的有效性，验证『对齐国际化权威』不仅是『有引用』且『引用有效』。带缓存，可增量。**口径**：403/418 及 crates.io 的 404 单列 anti_bot（站点对脚本 UA 反爬，链接本身可能有效，需浏览器人工复核），不计入失效 bad。

> 扫描 concept/+knowledge/+docs/ 权威域唯一 URL: **2111** · 真失效（不含反爬）: **0** · 反爬 403/418: **0** · crates.io 反爬 404: **1**

| 分级 | 真失效（不含反爬） | 反爬 403/418 | crates.io 反爬 404 |
|:---|---:|---:|---:|
| P0 | 0 | 0 | 1 |
| P1 | 0 | 0 | 0 |
| P2 | 0 | 0 | 0 |

✅ 本次扫描的权威域 URL 无真失效（2xx/3xx；403 反爬已单列）。

## crates.io 反爬 404（前 40，真实 crate/根页在浏览器中通常可达，不计入失效）

| 分级 | URL | 引用文件（≤3） |
|:---|:---|:---|
| P0 | <https://github.com/rust-lang/cargo/blob/master/src/cargo/util/toml/embedded.rs> | concept/06_ecosystem/01_cargo/01_cargo_script.md |

## 诚信

- 仅查 P0/P1/P2 权威域（单一来源：maintenance/authority_coverage_dashboard.py）；不查其它外部域。
- 403/418 及 crates.io 404 不视为『被对齐内容失效』：链接本身可能有效，仅是脚本 UA 被拦，需浏览器人工复核后决定是否保留。
- 瞬时网络抖动可能导致个别误判；真失效项需人工/后台查证新址后替换，勿据此脚本自动删正文。

*由 `scripts/check_authority_link_health.py` 生成*
