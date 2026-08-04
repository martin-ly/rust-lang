# 开发者导航一致性指南


## 📊 目录

- [1. 本地校验](#1-本地校验)
- [2. 启用 pre-commit 钩子](#2-启用-pre-commit-钩子)
- [3. CI 检查](#3-ci-检查)
- [4. 每周报告](#4-每周报告)
- [5. 规范摘要](#5-规范摘要)
- [6. 常见问题](#6-常见问题)


本指南说明如何在本地与CI中确保“返回知识图谱”导航区块的一致性。

## 1. 本地校验

```powershell
# 仅校验
.\scripts\navigation_injector.ps1 -Root . -CheckOnly

# 自动注入缺失导航
.\scripts\navigation_injector.ps1 -Root .
```

## 2. 启用 pre-commit 钩子

```powershell
# 复制钩子脚本到 Git Hooks 目录
Copy-Item scripts\pre-commit-hook.ps1 .git\hooks\pre-commit -Force

# 可选：设置执行权限（Windows 通常不需）
# icacls .git\hooks\pre-commit /grant Everyone:RX
```

启用后，每次提交将自动为新增 `.md`/`.rs` 文件注入导航区块。

## 3. CI 检查

- PR/Push 触发 `.github/workflows/navigation-check.yml`
- 若发现缺失导航，检查会失败并提示修复方式

## 4. 每周报告

- `.github/workflows/navigation-weekly.yml` 每周自动运行一次
- 生成文本报告作为构建产物，可在 Actions 页面下载

## 5. 规范摘要

- 文首：插入“返回知识图谱”导航区块（引用块 + 分隔线）
- 文末：插入“参考指引”行（节点映射、综合快照）
- Rust 源码：在文件头以注释形式加入上述链接

## 6. 常见问题

- 若相对路径不正确：手动检查文件相对 `formal_rust/refactor/` 的层级，或提交Issue
- 若脚本运行缓慢：可指定较小的 `-Root` 子目录进行增量处理
- 若需扩展文件类型：可在脚本顶部 `IncludeExtensions` 中添加扩展名
