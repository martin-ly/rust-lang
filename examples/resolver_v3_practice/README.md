# Resolver v3 Practice

> **定位**: Cargo Resolver v3 与 MSRV-aware 依赖解析实践。

---

## 内容

本 workspace 演示混合 MSRV（1.70 / 1.84 / 1.96）项目在使用 resolver v3 时的行为：

- `incompatible-rust-version = "fallback"` 策略
- `incompatible-rust-version = "allow"` 策略
- `cargo tree --duplicates` 诊断重复依赖

---

## 运行

```bash
cd examples/resolver_v3_practice
cargo check --workspace
cargo tree --duplicates
```

---

## 延伸阅读

- `concept/06_ecosystem/60_cargo_dependency_resolution.md`
