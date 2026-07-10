# resolver v3 / public dependency 演示

本 crate 演示 Cargo resolver v3 与 `public = true` 如何影响依赖 feature unification。

## 结构

- `crate-d`：底层库，提供 `serde` feature。
- `crate-b` / `crate-c`：中间库，分别依赖 `crate-d` 并公开/私有使用。
- 顶层 bin：通过 `public = true` 让 `crate-d` 的 feature 在最终 crate 中可见，同时避免中间 crate 内部 feature 污染。

## 运行

```bash
cargo tree -e features
```
