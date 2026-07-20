# OpenAPI 指南

- 推荐使用 `utoipa` 生成文档；CI 产出 `openapi.json` 工件
- 契约测试：可用 `schemars`/`jsonschema` 进行 schema 校验
- 版本与兼容性：语义化版本；新增字段默认可选；旧字段保留过渡期
