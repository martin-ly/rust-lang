# resolver v3 / public dependency 演示

本 crate 演示 Cargo resolver v3 与 `public = true` 如何影响依赖 feature unification。

## 结构

- `crate-d`：底层库，提供 `serde` feature。
- `crate-b` / `crate-c`：中间库，分别依赖 `crate-d` 并公开/私有使用。
- 顶层 bin：直接依赖 `crate-d` 并启用 `serde` feature，观察 feature unification 结果。

> 注：`public = true` 依赖目前为 nightly-only 特性（需 `-Zpublic-dependency`），稳定版 cargo 会忽略并告警，
> 因此 `crate-b` / `crate-c` 的 `Cargo.toml` 中仅以注释形式保留该写法。nightly 下可取消注释并用
> `cargo +nightly tree -Zpublic-dependency -e features` 观察公共依赖对 feature unification 的影响。

## 运行

```bash
cargo tree -e features
```
