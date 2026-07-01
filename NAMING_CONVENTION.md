# 命名规范

> **版本**: 1.0
> **生效日期**: 2026-06-28
> **适用范围**: 全仓库新增文件与目录（历史文件按过渡期例外清单处理）

---

## 1. 目标

- 保证跨平台（Linux/macOS/Windows）路径兼容
- 提高可发现性与可搜索性
- 便于脚本、CI 和自动化工具处理
- 消除中文、空格、大小写混用带来的不一致

## 2. 文件命名

### 2.1 Markdown 文件

- **基本格式**: `snake_case.md`
- **带编号前缀**: `number_prefix_snake_case.md`
  - 示例: `01_ownership.md`, `03_advanced_traits.md`
- 仅允许以下**全大写例外**:
  - `README.md`
  - `INDEX.md`
  - `CONTRIBUTING.md`
  - `CHANGELOG.md`
  - `SECURITY.md`
  - `CODE_OF_CONDUCT.md`
  - `LICENSE`
- 禁止使用中文、空格、连字符 `-`、CamelCase、PascalCase、特殊符号（下划线与数字除外）

### 2.2 脚本与源码文件

- Python: `snake_case.py`
- Shell: `snake_case.sh`
- Rust: `snake_case.rs`（bin/example 名称也建议 snake_case）
- TOML/YAML/JSON: `snake_case.toml`, `snake_case.yaml`, `snake_case.json`

### 2.3 图片与二进制资源

- 建议使用 `snake_case.ext`
- 必要时可用 `number_prefix_snake_case.ext`

## 3. 目录命名

- **基本格式**: `snake_case`
- **带编号前缀**: `number_prefix_snake_case`
  - 示例: `01_foundation`, `03_advanced`
- 顶层特殊目录保留（已存在）:
  - `.cargo`, `.github`, `.kimi`, `.vscode`
  - `archive`, `book`, `concept`, `content`, `crates`, `docs`, `examples`, `exercises`, `guides`, `k8s`, `knowledge`, `reports`, `scripts`, `supply-chain`, `target`, `theme`, `tools`

## 4. 禁止项

- 文件名或目录名中使用中文字符
- 空格、`\t`、换行符
- 除 `.`（扩展名分隔）和 `_` 之外的标点符号
- CamelCase / PascalCase（特殊保留名除外）

## 5. 过渡期例外

- 历史文件（提交日期早于 2026-06-28）可保留原名称，但新增引用时应使用规范名
- 脚本 `scripts/lint_filenames.py` 默认只检查本次变更的文件，不强制要求历史文件重命名

## 6. 检查工具

```bash
# 检查本次提交/PR 中变更的文件名
python scripts/lint_filenames.py

# 检查相对于某个基线的变更
python scripts/lint_filenames.py --since-ref origin/main
```
---

*本规范随 Phase 1 治理计划执行。*
