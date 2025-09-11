# c18_model 文档索引

> 构建文档站点：已提供 mdBook 配置（book.toml、SUMMARY.md）。

## Guides（使用指南）

- 总览：`guides/README.md`
- 系统建模推进：`guides/system-modeling.md`
- ML 预处理与评估：`guides/ml-preprocess-eval.md`
- 状态机到协议验证：`guides/fsm-to-protocol.md`

## API Reference（API 参考）

- 形式化模型：`api-reference/formal-models.md`
- 排队论模型：`api-reference/queueing-models.md`
- 机器学习模型：`api-reference/ml-models.md`

## Patterns（模式）

- 设计与实现模式：`patterns/README.md`

---

建议从 Guides 入手，结合 API Reference 查阅具体接口；遇到工程落地问题时参考 Patterns 的“最佳实践/反模式”。

## 构建与预览（mdBook）

1. 安装 mdBook：`cargo install mdbook`
2. 本地预览：在 `crates/c18_model/docs` 目录执行 `mdbook serve -n 127.0.0.1 -p 3000`，浏览器打开 `http://127.0.0.1:3000`
3. 生成静态站点：`mdbook build`（输出在 `book/`）

## GitHub Pages 发布

- 工作流：`.github/workflows/mdbook.yml` 已配置自动构建与 Pages 部署
- 首次启用：在仓库 Settings → Pages 中选择 Deployment: GitHub Actions
- 部署产物：由工作流上传 Pages Artifact，内容为 `crates/c18_model/docs/book`
