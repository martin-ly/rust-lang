---
title: repr(packed) 安全注意事项
lang: zh-CN
---

要点：

- `#[repr(packed)]` 会移除对齐，按字节紧凑布局；直接取字段引用可能产生未对齐引用，UB！
- 读取 packed 字段应使用按值复制（`copy`）或 `ptr::read_unaligned`/`write_unaligned`。
- FFI/IO 结构体解析常见；尽量使用 bytemuck/zerocopy 等库辅助。

示例与测试：见 `examples/repr_packed_safety.rs` 与 `tests/repr_packed_safety_tests.rs`。
