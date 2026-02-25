# Rust 新版本发布追踪 Checklist

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **归档日期**: 2026-02-20
> **归档原因**: 过程性文档归档
> **状态**: 📦 已归档

---


> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: Rust 新版本发布后的文档与配置更新流程

---

## 触发时机

- Rust 稳定版发布（通常每 6 周）
- 官方公告：<https://blog.rust-lang.org/releases/>
- 详细 changelog：<https://releases.rs/>

---

## 代码示例

### 版本发布检查自动化脚本

```rust
//! Rust 新版本发布检查清单自动化
use std::collections::HashMap;
use std::fs;
use std::process::Command;

struct ReleaseChecklist {
    version: String,
    checks: Vec<CheckItem>,
}

struct CheckItem {
    category: String,
    description: String,
    command: Option<String>,
    manual: bool,
}

impl ReleaseChecklist {
    fn new(version: &str) -> Self {
        let checks = vec![
            // 1. 获取权威信息
            CheckItem {
                category: "权威信息".to_string(),
                description: "阅读 Rust Blog 发布公告".to_string(),
                command: Some("curl -s https://blog.rust-lang.org/releases/".to_string()),
                manual: true,
            },
            CheckItem {
                category: "权威信息".to_string(),
                description: "阅读 releases.rs 详细 changelog".to_string(),
                command: Some("curl -s https://releases.rs/".to_string()),
                manual: true,
            },

            // 2. 更新 toolchain 文档
            CheckItem {
                category: "Toolchain 文档".to_string(),
                description: format!("创建 rust_{}_vs_对比文档", version),
                command: None,
                manual: true,
            },

            // 3. 更新版本声明
            CheckItem {
                category: "版本声明".to_string(),
                description: "更新根 Cargo.toml rust-version".to_string(),
                command: Some("cargo check".to_string()),
                manual: false,
            },

            // 8. 验证
            CheckItem {
                category: "验证".to_string(),
                description: "cargo build 通过".to_string(),
                command: Some("cargo build --workspace".to_string()),
                manual: false,
            },
            CheckItem {
                category: "验证".to_string(),
                description: "cargo test 通过".to_string(),
                command: Some("cargo test --workspace".to_string()),
                manual: false,
            },
            CheckItem {
                category: "验证".to_string(),
                description: "doc-test 通过（含 compile_fail）".to_string(),
                command: Some("cargo test -p c01_ownership_borrow_scope --doc".to_string()),
                manual: false,
            },
        ];

        Self {
            version: version.to_string(),
            checks,
        }
    }

    fn execute_check(&self, check: &CheckItem) -> Result<(), String> {
        if check.manual {
            println!("⚠️  手动检查: {}", check.description);
            return Ok(());
        }

        if let Some(cmd) = &check.command {
            println!("执行: {}", cmd);
            let output = Command::new("sh")
                .args(["-c", cmd])
                .output()
                .map_err(|e| format!("执行失败: {}", e))?;

            if !output.status.success() {
                return Err(format!(
                    "命令失败: {}",
                    String::from_utf8_lossy(&output.stderr)
                ));
            }
        }

        Ok(())
    }

    fn run_all(&self) {
        println!("=== Rust {} 发布检查清单 ===\n", self.version);

        let mut passed = 0;
        let mut failed = 0;

        for check in &self.checks {
            print!("[{}] {}... ", check.category, check.description);

            match self.execute_check(check) {
                Ok(_) => {
                    println!("✅");
                    passed += 1;
                }
                Err(e) => {
                    println!("❌ - {}", e);
                    failed += 1;
                }
            }
        }

        println!("\n=== 结果 ===");
        println!("通过: {}, 失败: {}", passed, failed);
    }

    fn generate_markdown(&self) -> String {
        let mut output = format!(
            "# Rust {} 发布追踪 Checklist\n\n",
            self.version
        );

        let mut current_category = String::new();

        for check in &self.checks {
            if check.category != current_category {
                output.push_str(&format!("\n### {}\n\n", check.category));
                current_category = check.category.clone();
            }

            output.push_str(&format!("- [ ] {}\n", check.description));
        }

        output
    }
}

fn main() {
    let checklist = ReleaseChecklist::new("1.93");
    checklist.run_all();

    // 生成 Markdown 版本
    fs::write("RELEASE_CHECKLIST_1.93.md", checklist.generate_markdown()).unwrap();
    println!("\n检查清单已保存: RELEASE_CHECKLIST_1.93.md");
}
```

### 批量更新版本元数据

```rust
//! 批量更新文档中的版本元数据
use std::fs;
use regex::Regex;

struct VersionMetadataUpdater {
    old_version: String,
    new_version: String,
    updated_files: Vec<String>,
}

impl VersionMetadataUpdater {
    fn new(old_version: &str, new_version: &str) -> Self {
        Self {
            old_version: old_version.to_string(),
            new_version: new_version.to_string(),
            updated_files: Vec::new(),
        }
    }

    fn update_file(&mut self, path: &str) -> Result<(), String> {
        let content = fs::read_to_string(path)
            .map_err(|e| format!("读取失败: {}", e))?;

        let mut new_content = content.clone();

        // 更新版本声明
        let version_pattern = Regex::new(&format!(
            r"(Rust 版本.*?: *)({})",
            regex::escape(&self.old_version)
        )).unwrap();
        new_content = version_pattern.replace_all(&new_content,
            format!("${{1}}{}", self.new_version)
        ).to_string();

        // 更新最后更新日期
        let today = chrono::Local::now().format("%Y-%m-%d").to_string();
        let date_pattern = Regex::new(r"> \*\*最后更新\*\*: .*").unwrap();
        new_content = date_pattern.replace_all(&new_content,
            format!("> **最后更新**: {}"), today
        ).to_string();

        if content != new_content {
            fs::write(path, new_content)
                .map_err(|e| format!("写入失败: {}", e))?;
            self.updated_files.push(path.to_string());
        }

        Ok(())
    }

    fn update_directory(&mut self, dir: &str) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().map_or(false, |e| e == "md") {
                    let _ = self.update_file(&path.to_string_lossy());
                }
            }
        }
    }

    fn report(&self) {
        if self.updated_files.is_empty() {
            println!("没有文件需要更新");
        } else {
            println!("已更新 {} 个文件:", self.updated_files.len());
            for file in &self.updated_files {
                println!("  - {}", file);
            }
        }
    }
}

fn main() {
    let mut updater = VersionMetadataUpdater::new("1.92.0", "1.93.0");

    // 更新关键目录
    updater.update_directory("docs/02_reference/quick_reference");
    updater.update_directory("docs/06_toolchain");
    updater.update_directory("docs/07_project");

    updater.report();
}
```

### 权威源日期同步检查

```rust
//! 检查并更新权威源同步日期
use std::fs;
use regex::Regex;
use chrono::Local;

struct AuthoritativeSourceSyncChecker;

impl AuthoritativeSourceSyncChecker {
    fn check_file(path: &str) -> Option<String> {
        let content = fs::read_to_string(path).ok()?;

        // 检查是否包含权威源日期标记
        let date_pattern = Regex::new(r"最后对照 releases\.rs: (\d{4}-\d{2}-\d{2})").unwrap();

        if let Some(captures) = date_pattern.captures(&content) {
            let last_date = captures.get(1)?.as_str();
            let today = Local::now().format("%Y-%m-%d").to_string();

            // 如果超过 30 天未更新，提示需要更新
            let days_diff = Self::days_between(last_date, &today);

            if days_diff > 30 {
                return Some(format!(
                    "⚠️  超过 30 天未更新 ({}天前)",
                    days_diff
                ));
            } else {
                return Some(format!(
                    "✅ {} 天内已更新",
                    days_diff
                ));
            }
        }

        Some("❌ 缺少权威源日期标记".to_string())
    }

    fn days_between(date1: &str, date2: &str) -> i64 {
        // 简化计算，实际应使用 chrono::NaiveDate
        0
    }

    fn update_date(path: &str) -> Result<(), String> {
        let content = fs::read_to_string(path)
            .map_err(|e| format!("读取失败: {}", e))?;

        let today = Local::now().format("%Y-%m-%d").to_string();

        // 更新日期
        let date_pattern = Regex::new(r"(最后对照 releases\.rs: )\d{4}-\d{2}-\d{2}").unwrap();
        let new_content = date_pattern.replace_all(&content,
            format!("${{1}}{}", today)
        );

        fs::write(path, new_content.as_ref())
            .map_err(|e| format!("写入失败: {}", e))?;

        Ok(())
    }

    fn check_toolchain_docs() {
        let toolchain_dir = "docs/06_toolchain";

        println!("=== 权威源日期同步检查 ===\n");

        if let Ok(entries) = fs::read_dir(toolchain_dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().map_or(false, |e| e == "md") {
                    let path_str = path.to_string_lossy();
                    if let Some(status) = Self::check_file(&path_str) {
                        println!("{}: {}", path.file_name().unwrap().to_string_lossy(), status);
                    }
                }
            }
        }
    }
}

fn main() {
    AuthoritativeSourceSyncChecker::check_toolchain_docs();
}
```

---

## 形式化链接

### 研究笔记关联

- **版本演进**: [08_rust_version_evolution_1.89_to_1.93.md](../../../../06_toolchain/08_rust_version_evolution_1.89_to_1.93.md) - 版本演进链
- **兼容性分析**: [09_rust_1.93_compatibility_deep_dive.md](../../../../06_toolchain/09_rust_1.93_compatibility_deep_dive.md) - 兼容性深度分析
- **模块适配**: [MODULE_1.93_ADAPTATION_STATUS.md](./MODULE_1.93_ADAPTATION_STATUS.md) - 各模块适配状态

### 实施场景

| 场景 | 实施步骤 | 参考代码 |
| :--- | :--- | :--- |
| **新版本发布** | 1. 运行检查清单自动化脚本<br>2. 逐一验证手动检查项<br>3. 生成进度报告 | `ReleaseChecklist::run_all()` |
| **批量版本更新** | 1. 使用元数据更新器<br>2. 批量更新文档版本声明<br>3. 验证更新结果 | `VersionMetadataUpdater` |
| **季度审查** | 1. 检查权威源日期<br>2. 更新过期日期标记<br>3. 生成审查报告 | `AuthoritativeSourceSyncChecker` |

---

## Checklist

### 1. 获取权威信息

- [ ] 阅读 [Rust Blog 发布公告](https://blog.rust-lang.org/releases/)
- [ ] 阅读 [releases.rs 详细 changelog](https://releases.rs/)
- [ ] 记录破坏性变更与未来不兼容警告

### 2. 更新 toolchain 文档

- [ ] 新建 `docs/06_toolchain/0X_rust_1.XX_vs_1.YY_comparison.md`（或更新序号）
- [ ] 更新 [toolchain/README.md](../../../../06_toolchain/README.md) 文档列表
- [ ] 新建 `docs/06_toolchain/0X_rust_1.XX_compatibility_notes.md`（若有兼容性变更）
- [ ] 更新 [08_rust_version_evolution](../../../../06_toolchain/08_rust_version_evolution_1.89_to_1.93.md) 或新建演进链

### 3. 更新版本声明

- [ ] 根 [Cargo.toml](../../../../../Cargo.toml) 中 `rust-version`
- [ ] [Cargo.workspace](../../../../../Cargo.workspace) 中 `target-rust-version`
- [ ] 各 crate 的 `rust-version`（c01–c12）

### 4. 更新速查卡

- [ ] 批量更新 `docs/02_reference/quick_reference/*.md` 中的「Rust 版本」元数据
- [ ] 更新 [quick_reference/README.md](../../../../02_reference/quick_reference/README.md) 版本声明

### 5. 更新思维表征

- [ ] 更新 [THINKING_REPRESENTATION_METHODS.md](../../../../04_thinking/THINKING_REPRESENTATION_METHODS.md) 中的版本特性思维导图
- [ ] 更新 [MULTI_DIMENSIONAL_CONCEPT_MATRIX.md](../../../../04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md)（若有新选型维度）

### 6. 更新权威源同步日期（权威源元数据规范）

- [ ] 在 [07_rust_1.93_full_changelog.md](../../../../06_toolchain/07_rust_1.93_full_changelog.md) 等 toolchain 文档末尾更新「最后对照 releases.rs: YYYY-MM-DD」
- [ ] 规范：所有 `docs/06_toolchain/*.md` 文档应在文末或元数据中包含「最后对照 releases.rs: 日期」，便于可维护性与可信度

### 7. 更新模块适配状态

- [ ] 更新 [MODULE_1.93_ADAPTATION_STATUS.md](./MODULE_1.93_ADAPTATION_STATUS.md)（或对应版本表）
- [ ] 在相关 crate 中增加新版本 API 示例（若有稳定化 API）

### 8. 验证

- [ ] `cargo build` 通过
- [ ] `cargo test` 通过
- [ ] `cargo test -p c01_ownership_borrow_scope --doc` 通过（含 compile_fail 反例）
- [ ] 检查文档断链：`./scripts/check_links.ps1` 或 `cargo deadlinks`（若已安装）

---

## 季度审查（每季度执行一次）

- [ ] 检查 [DECISION_GRAPH_NETWORK](../../../../04_thinking/DECISION_GRAPH_NETWORK.md)、[PROOF_GRAPH_NETWORK](../../../../04_thinking/PROOF_GRAPH_NETWORK.md) 等引用是否有效
- [ ] 核对各模块 README 中的版本声明与兼容性链接
- [ ] 确认 [10_rust_1.89_to_1.93_cumulative_features_overview](../../../../06_toolchain/10_rust_1.89_to_1.93_cumulative_features_overview.md) 等累积文档是否需要扩展
- [ ] 更新「最后对照 releases.rs」日期（见 [07_rust_1.93_full_changelog](../../../../06_toolchain/07_rust_1.93_full_changelog.md) 末尾）

---

## 模板：新版本对比文档结构

```markdown
# Rust 1.XX vs 1.YY 全面对比分析

- 版本概览
- 核心改进（3–5 项）
- 标准库更新
- 编译器改进
- 工具链更新
- 迁移指南
- 参考资源
```

---

## 相关文档

- [Rust 1.93 vs 1.92 对比](../../../../06_toolchain/05_rust_1.93_vs_1.92_comparison.md)
- [Rust 1.93 兼容性注意事项](../../../../06_toolchain/06_rust_1.93_compatibility_notes.md)
- [版本演进链](../../../../06_toolchain/08_rust_version_evolution_1.89_to_1.93.md)
- [各模块 1.93 适配状态一览表](./MODULE_1.93_ADAPTATION_STATUS.md)
