# 契约测试

- REST：基于 OpenAPI 生成客户端校验用例；可用记录/回放（VCR）降低依赖波动
- gRPC：基于 `.proto` 生成的 stub 做端到端用例；断言响应 schema 与语义
- 破坏性变更检测：CI 对比上版契约（OpenAPI/Proto）并阻断
