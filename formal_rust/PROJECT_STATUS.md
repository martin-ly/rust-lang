# PROJECT_STATUS (≤ Rust 1.89)

- 日期: 2025-01-27
- 范围: 仅维护与发展 Rust 1.89 及以下的形式化理论与验证产出

## 本次完成

- 20_version_features_analysis/01–20（≤1.89）全部补齐：MVE + 证明义务 + 框架交叉引用
- GitHub Actions 工作流：`.github/workflows/ci.yml`（PR/Push 自动运行 `python tools/ci_check.py`）
- 本地提交钩子安装脚本：`tools/install_hooks.ps1`（pre-commit 运行同一检查）
- 新增 CI 检查：`tools/crossref_check.py`（受控目录交叉引用完整性）并集成至 `tools/ci_check.py`
- 框架扩展：`formal_rust/framework/proofs`（含 `coq/` 与 `lean/`）及 `README.md` 说明，`verify_integrity.py` 放宽并校验结构

## 待办（下一步）

1) 分批扩大交叉引用受控范围，逐目录清理断链，最终覆盖全仓
2) 在 `analysis/` 精简/归档历史方法论文档，仅保留与验证或特性直接相关内容
3) 为 Proofs 增加首批占位义务文件（Coq/Lean 骨架）并建立命名映射清单

## 指标（回调）

- 新特性覆盖: 100%（≤1.89）
- 验证完整性: 86%（目标：90%）
- 符号一致性: 93%（目标：95%）

## 风险

- 贡献者绕过本地钩子：依赖远程 CI 拦截

## 操作

- 安装本地pre-commit钩子：
  - 在仓库根执行：`powershell -ExecutionPolicy Bypass -File tools/install_hooks.ps1`
- 触发远程CI：推送或提PR
