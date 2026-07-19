# CI 集成（API 契约）

- 导出：构建时导出 `openapi.json` 与 `.proto` 归档为工件
- 校验：
  - OpenAPI：使用 `openapi-diff` 对比上版是否有破坏性变更
  - Protobuf：通过自定义脚本校验字段新增/删除/重号
- 门禁：若检测到破坏性变更，阻断 PR 合入；需提供兼容性说明与迁移计划
