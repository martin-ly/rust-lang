# Rust 1.89→1.93 累积特性总览

> **创建日期**: 2026-02-12
> **Rust 版本**: 1.93.0+
> **用途**: 1.89 至 1.93 五个版本累积语言/库/兼容性变更一览

---

## 总览表

| 版本 | 发布日期 | 语言 | 库 | 兼容性 | 平台 |
|------|----------|------|-----|--------|------|
| 1.89 | 2025-08 | - | - | - | - |
| 1.90 | 2025-09 | - | - | LLD 默认 | x86_64-apple-darwin 等 |
| 1.91 | 2025-10 | dangling_pointers_from_locals | - | warn-by-default | aarch64-pc-windows-msvc Tier 1 |
| 1.92 | 2025-12 | Never 类型 Lint 严格化 | Box/Rc/Arc::new_zeroed、迭代器特化 | deny-by-default | musl 预告 |
| 1.93 | 2026-01 | s390x、C variadic、LUB coercion、asm_cfg | MaybeUninit、String/Vec、VecDeque、Duration、char、fmt | deref_nullptr、#[test]、offset_of、repr(C) enum | musl 1.2.5、riscv64a23 Tier 2 |

---

## 语言特性累积（1.89→1.93）

| 特性 | 版本 | 说明 |
|------|------|------|
| LLD 默认链接器 | 1.90 | x86_64-unknown-linux-gnu |
| dangling_pointers_from_locals | 1.91 | 局部悬垂指针 lint |
| Never 类型 Lint 严格化 | 1.92 | never_type_fallback_flowing_into_unsafe、dependency_on_unit_never_type_fallback |
| s390x C-style variadic | 1.93 | variadic 函数调用 |
| LUB coercion | 1.93 | 最小上界强制转换 |
| asm_cfg | 1.93 | cfg 属性在 asm! 行上 |
| const_item_interior_mutations | 1.93 | const 项内部可变 |
| function_casts_as_integer | 1.93 | 函数指针转整数 |

---

## 标准库 API 累积（1.89→1.93）

| 类别 | 版本 | API |
|------|------|-----|
| 零初始化 | 1.92 | Box::new_zeroed、Rc::new_zeroed、Arc::new_zeroed |
| MaybeUninit | 1.93 | 新方法（write_copy_of_slice 等） |
| String/Vec | 1.93 | into_raw_parts、from_raw_parts |
| VecDeque | 1.93 | pop_front_if、pop_back_if |
| 整数 | 1.93 | unchecked_add、unchecked_sub 等 |
| 切片 | 1.93 | slice.as_array() |
| Duration | 1.93 | from_nanos_u128 |
| char | 1.93 | MAX_LEN_UTF8、MAX_LEN_UTF16 |
| fmt | 1.93 | fmt::from_fn |

### 行为变更（1.93）

| 变更 | 影响 |
|------|------|
| Copy specialization 移除 | 可能性能回归 |
| BTreeMap::append | 相同 key 不再覆盖，保留目标 |
| vec::IntoIter | 实现 RefUnwindSafe |

---

## 兼容性变更累积（1.89→1.93）

| 变更 | 版本 | 详情 |
|------|------|------|
| LLD 默认 | 1.90 | 链接器行为 |
| dangling_pointers_from_locals | 1.91 | warn-by-default |
| Never 类型 Lint | 1.92 | deny-by-default |
| deref_nullptr | 1.93 | deny-by-default |
| #[test] 无效位置 | 1.93 | 报错 |
| offset_of! 类型检查 | 1.93 | 更严格 |
| ... 可变参数 | 1.93 | future-incompat |
| repr(C) enum 警告 | 1.93 | 新警告 |
| pin_v2 | 1.93 | Pin API 变更 |
| Emscripten unwinding | 1.93 | ABI 变更 |

---

## 平台支持累积（1.89→1.93）

| 平台 | 版本 | 变更 |
|------|------|------|
| x86_64-apple-darwin | 1.90 | 支持调整 |
| aarch64-pc-windows-msvc | 1.91 | Tier 1 |
| musl 1.2.5 | 1.93 | DNS 解析改进 |
| riscv64a23-unknown-linux-gnu | 1.93 | Tier 2 |

---

## 工具链累积

| 工具 | 1.93 变更 |
|------|-----------|
| Cargo | publish --workspace（1.90）、依赖解析 |
| Clippy | 新 lint |
| Rustfmt | 格式化规则 |

---

## 相关文档

| 文档 | 路径 |
|------|------|
| 版本演进链 | [08_rust_version_evolution_1.89_to_1.93.md](./08_rust_version_evolution_1.89_to_1.93.md) |
| 1.93 vs 1.92 | [05_rust_1.93_vs_1.92_comparison.md](./05_rust_1.93_vs_1.92_comparison.md) |
| 1.93 兼容性深度 | [09_rust_1.93_compatibility_deep_dive.md](./09_rust_1.93_compatibility_deep_dive.md) |
| 1.93 完整变更 | [07_rust_1.93_full_changelog.md](./07_rust_1.93_full_changelog.md) |
| 发布追踪清单 | [../RUST_RELEASE_TRACKING_CHECKLIST.md](../RUST_RELEASE_TRACKING_CHECKLIST.md) |
