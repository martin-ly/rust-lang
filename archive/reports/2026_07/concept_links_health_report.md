# concept/ 全量链接健康检查报告

> 生成时间: 2026-06-21
> 扫描范围: `concept/` 下 337 个 Markdown 文件中的全部 Markdown 链接
> 检查对象: Rust 官方、生态 crate、学术/跨语言、平台集成等权威域名（不含 `github.com`，避免反爬虫误判）

## 检查结果

| 指标 | 数值 |
|:---|:---|
| 检查链接数 | 1619（去重后） |
| HTTP 200 | 1619 |
| 404 / 异常 | 0 |

## 本轮主要修复类别

| 类别 | 示例修复 | 涉及文件数 |
|:---|:---|---:|
| RFC 链接 slug 补全/无效 RFC 转 PR | `rfcs/3513.html` → `rfcs/3513-gen-blocks.html` | 78 |
| 官方 doc.rust-lang.org 路径迁移 | `reference/ownership.html` → `book/ch04-00-understanding-ownership.html` | 50 |
| 官方链接二次修正 | `std/num/NonZeroU32.html` → `std/num/type.NonZeroU32.html` | 12 |
| rustc-dev-guide 结构调整 | `rustc-driver.html` → `rustc-driver/intro.html` | 约 30 |
| wasm-bindgen / wasm-pack 文档迁移 | `rustwasm.github.io/wasm-bindgen/` → `rustwasm.github.io/docs/wasm-bindgen/` | 8 |
| rust-unofficial patterns 页面调整 | 指向 `print.html` 锚点或根 | 多个 |
| 生态站点结构变化 | Bevy book、TikV docs、serde.rs、TLBORM 等 | 多个 |
| 博客 URL 补齐年份 / 替换失效文章 | `inside-rust/08/20/...` → `inside-rust/2025/08/20/...` | 14 |

## 脚本改进

- 新增 `scripts/check_all_concept_links_health.py`：扫描 `concept/` 下全部 Markdown 链接（不仅是 `来源:` 块）。
- 新增/更新修复脚本：
  - `scripts/fix_rfcs.py`
  - `scripts/fix_official_and_ecosystem_links.py`
  - `scripts/fix_remaining_concept_links.py`
  - `scripts/fix_double_and_misc_links.py`
  - `scripts/fix_corrupted_urls.py`
  - `scripts/fix_final_broken_links.py`
- `check_all_concept_links_health.py` 增加 HEAD 失败后的 GET 回退，减少 `Accept` 头缺失导致的误报。
- 暂时将 `github.com` 移出全量扫描域名：GitHub 对高频 HEAD 请求敏感，易出现 500/404 波动，后续可单独通过 GitHub API 检查。

## 回归验证

| 检查项 | 结果 |
|:---|:---|
| `concept/` 非 GitHub 权威链接 | **0 异常** |
| `concept/` 来源块扩展权威链接 | **0 异常** |
| i18n 元数据覆盖率 | EN/Summary/来源 337/337 |
| 代码块编译 | **2118/2118 通过** |

## 说明

- 本次扫描覆盖 `concept/` 内所有 Markdown 链接，较之前仅检查 `> **来源**:` 块的策略更全面。
- `github.com` 链接未纳入本次自动判定；已人工修复其中确认的失效链接（如 WASI、wasm-pack、部分 RFC PR 等）。
