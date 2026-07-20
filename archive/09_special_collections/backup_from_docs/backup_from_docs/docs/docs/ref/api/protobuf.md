# Protobuf/gRPC 指南

- 使用 `tonic` + `prost`；统一代码生成路径与模块组织
- 兼容策略：字段只增不删；避免重用已弃用编号
- 契约测试：golden files 比对 `.proto` 生成物与服务行为
