# Cross-Domain Semantic Coverage Baseline Report (2026_07_15)

> 检查 Rust 1.97 关键交叉/边界语义域在 `concept/` 中是否有非 stub 权威页。

## 汇总

- 总主题数：16
- 已覆盖：16 (100.0%)
- 未覆盖：0

## 未覆盖主题

未发现。

## 已覆盖主题

- ✅ `01_foundation/04_control_flow/03_let_chains.md` — let chains / if-let guards
- ✅ `03_advanced/04_ffi/05_unsafe_extern_blocks.md` — unsafe extern blocks (Edition 2024)
- ✅ `03_advanced/02_unsafe/08_async_in_unsafe_contexts.md` — async + unsafe boundary
- ✅ `03_advanced/04_ffi/04_async_ffi_boundary.md` — FFI + async boundary
- ✅ `06_ecosystem/05_systems_and_embedded/11_async_no_std_embedded.md` — no_std + async
- ✅ `02_intermediate/01_generics/05_const_generics_and_trait_objects.md` — const generics + trait objects
- ✅ `03_advanced/01_async/14_gat_async_boundary.md` — GAT + async
- ✅ `03_advanced/00_concurrency/04_send_sync_boundaries.md` — Send/Sync boundary in trait objects / closures / async state machines
- ✅ `03_advanced/01_async/11_pin_projection_counterexamples.md` — Pin projection + structural projection
- ✅ `03_advanced/06_low_level_patterns/01_custom_allocators.md` — allocator_api / per-container allocators
- ✅ `01_foundation/04_control_flow/02_patterns.md` — match ergonomics / default binding mode in Edition 2024
- ✅ `04_formal/05_rustc_internals/09_destructors.md` — temporary scope / tail expression drop (Edition 2024)
- ✅ `07_future/02_preview_features/06_const_trait_impl_preview.md` — const trait impl (effects system)
- ✅ `07_future/02_preview_features/17_type_alias_impl_trait_preview.md` — RTN / RPITIT / TAIT precise capturing
- ✅ `03_advanced/01_async/01_async.md` — async fn / Future equivalence + Send across await
- ✅ `03_advanced/02_unsafe/01_unsafe.md` — unsafe op in unsafe fn (Edition 2024)

## 主题清单维护说明

清单位于 `scripts/check_cross_domain_coverage.py` 的 `CROSS_DOMAIN_TOPICS` 字典。
新增主题时，需给出候选 `concept/` 权威页路径；覆盖标准：任一候选存在且非 stub。
