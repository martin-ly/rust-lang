# 定期维护检查清单

> **更新周期**: 每两周（bi-weekly）
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)
> **最后更新**: 2026-05-30

---

## 一、编译与测试验证

| 检查项 | 命令 | 通过标准 | 优先级 |
| :--- | :--- | :--- | :---: |
| 构建 | `cargo build --workspace` | 零错误零警告 | 🔴 |
| 测试 | `cargo test --workspace` | 3,597+ passed, 0 failed | 🔴 |
| Clippy | `cargo clippy --all-targets` | 零 lint | 🔴 |
| 格式化 | `cargo fmt --all -- --check` | 无差异 | 🟡 |
| 文档 | `cargo doc --workspace --no-deps` | 无文档警告 | 🟡 |
| Miri | `cargo miri test --workspace` (Linux) | Tree Borrows 通过 | 🟢 |

---

## 二、死链检查

| 检查项 | 命令 | 通过标准 | 优先级 |
| :--- | :--- | :--- | :---: |
| 内部链接 | `python scripts/check_links.py` | 损坏链接 ≤ 5（允许报告自引用/代码误报） | 🔴 |
| 外部链接 | `lychee docs/ README.md CHANGELOG.md` | 无新增 404 | 🟡 |

> **说明**: 当前基线为 4 个损坏链接（全部系报告自引用/代码误报）。若超过 5 个，需立即修复。

---

## 三、依赖安全审计

| 检查项 | 命令 | 通过标准 | 优先级 |
| :--- | :--- | :--- | :---: |
| 安全漏洞 | `cargo audit` | 0 高危漏洞 | 🔴 |
| 过期依赖 | `cargo outdated -R` | 无重大版本滞后 | 🟡 |
| 许可证兼容 | `cargo deny check licenses` | 无冲突 | 🟢 |

---

## 四、文档质量检查

| 检查项 | 方法 | 通过标准 | 优先级 |
| :--- | :--- | :--- | :---: |
| 受众标签 | `grep -r "**受众**:" concept/` | 覆盖率 100%（除 README/SUMMARY） | 🔴 |
| A/B/C 分级 | `grep -r "**分级**:" docs/` | 覆盖率 100%（除 archive/） | 🔴 |
| L4 形式化声明 | `grep -r "⚠️ **声明**" concept/04_formal/` | 覆盖率 100% | 🔴 |
| 术语表更新 | 检查新增术语 | 与最新 Rust 版本同步 | 🟡 |
| CHANGELOG | 检查遗漏变更 | 每次重大变更后更新 | 🟡 |

---

## 五、Rust 版本追踪

| 检查项 | 方法 | 通过标准 | 优先级 |
| :--- | :--- | :--- | :---: |
| 工具链 | `rustup show` | nightly 通道最新版 | 🔴 |
| MSRV | `Cargo.toml` rust-version | 与目标稳定版一致 | 🔴 |
| 新特性 | 官方 Release Notes | 及时更新 `rust_1_XX_features.rs` | 🟡 |
| WASI 目标 | `rustup target list` | `wasm32-wasip1`/`wasip2` | 🟡 |

---

## 六、CI/CD 健康检查

| 检查项 | 方法 | 通过标准 | 优先级 |
| :--- | :--- | :--- | :---: |
| CI 工作流 | `.github/workflows/` | 无失败 job | 🔴 |
| 工具链一致 | 检查所有 workflow | stable/nightly 统一 | 🔴 |
| 缓存配置 | `actions/cache` | 命中率高 | 🟢 |

---

## 七、归档管理

| 检查项 | 方法 | 通过标准 | 优先级 |
|:---|:---|:---|:---:|
| 历史版本 | `docs/archive/` | 每 3 版本保留 | 🟡 |
| 重复文件 | 相似度扫描 | 无新增 >60% 重复 | 🟡 |
| 旧报告 | `archive/` | 季度清理过期报告 | 🟢 |

---

## 快速执行脚本

```bash
# 编译测试三元组
cargo build --workspace && cargo test --workspace && cargo clippy --all-targets

# 死链检查
python scripts/check_links.py

# 安全审计
cargo audit

# 文档质量抽样（concept/ 目录）
python -c "
import os
for root, dirs, files in os.walk('concept'):
    for f in files:
        if f.endswith('.md'):
            path = os.path.join(root, f)
            with open(path) as fh:
                content = fh.read()
            if '**受众**' not in content and f not in ['README.md', 'SUMMARY.md']:
                print(f'Missing audience: {path}')
"
```

---

> **维护者**: Rust 学习项目团队
> **文档版本**: 1.0
> **状态**: ✅ 已创建
