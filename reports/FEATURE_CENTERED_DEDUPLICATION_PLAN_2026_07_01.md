# Feature-Centered Deduplication Plan: Rust 1.95 / 1.96 / 1.97 & Edition 2024

> **Scope**: Consolidate version-centric Rust feature documentation scattered across
> `concept/07_future/`, `knowledge/06_ecosystem/emerging/`, `docs/06_toolchain/`,
> `docs/02_reference/quick_reference/`, and `docs/research_notes/`.
>
> **Source overlap report**: `reports/PHASE0_CONTENT_OVERLAP_2026_07_01.md`
>
> **Status**: Read-only analysis; no file moves or content edits performed.
>
> **Date**: 2026-07-01

---

## 1. Consolidation Principles

| Principle | Rule |
|---|---|
| **Single authoritative source** | `concept/` owns the canonical explanation for every Rust version/theme. |
| **Feature-centric over version-centric** | Stable release pages act as **release indexes** that link to feature-specific concept files (e.g. `assert_matches`, `range_types`, `async_closures`). |
| **docs/ = lens/summary** | `docs/06_toolchain/` provides toolchain-specific summaries; `docs/02_reference/quick_reference/` provides cheat-sheet summaries. Both must point to the `concept/` source. |
| **knowledge/ = redirect or deep-dive only** | `knowledge/06_ecosystem/emerging/` becomes a redirect layer. Unique deep-dives (e.g. safety-critical analysis) are merged into the canonical concept file or moved to the relevant feature directory. |
| **research_notes/ = archive/redirect** | Research-note duplicates are archived with a header + link to the canonical concept file. |
| **Naming** | Follow existing conventions: `concept/07_future/rust_1_XX_stabilized.md` for stable releases; `rust_1_XX_preview.md` for pre-release tracking. |

---

## 2. Current File Map & Duplication Pairs

### 2.1 Rust 1.95

| File | Current role | Overlap pair from `PHASE0` |
|---|---|---|
| `concept/07_future/05_rust_version_tracking.md` | Cross-version formal-model tracker (contains 1.95 section) | — |
| `knowledge/06_ecosystem/emerging/03_rust_1_95.md` | Redirect to `docs/06_toolchain/06_14...` | vs `docs/06_toolchain/06_14_rust_1_95_nightly_preview.md` (0.60) |
| `knowledge/06_ecosystem/emerging/04_rust_1_95_preview.md` | Redirect to `docs/06_toolchain/06_14...` | vs `docs/06_toolchain/06_14_rust_1_95_nightly_preview.md` (0.60) |
| `docs/06_toolchain/06_14_rust_1_95_nightly_preview.md` | Self-declared authority; mixes stable 1.95 + nightly experiments | vs above |
| `docs/02_reference/quick_reference/02_rust_195_features_cheatsheet.md` | Stable 1.95 cheat sheet | (not in top-30 pairs, but content duplicates stable features) |
| `knowledge/04_expert/safety_critical/01_mind_maps/03_rust_194_195_features_deep_dive.md` | Safety-critical deep dive for 1.94/1.95 | vs `docs/research_notes/10_rust_194_195_feature_matrix.md` (0.75) |
| `docs/research_notes/10_rust_194_195_feature_matrix.md` | 1.94/1.95 feature matrix + formal tracking | vs above |

### 2.2 Rust 1.96

| File | Current role | Overlap pair from `PHASE0` |
|---|---|---|
| `concept/07_future/rust_1_96_stabilized.md` | **Project authority** for 1.96 | vs `knowledge/06_ecosystem/emerging/05_rust_1_96.md` (0.75), `docs/06_toolchain/06_22_rust_1_96_features.md` (0.75), `docs/06_toolchain/06_21_rust_1_97_features.md` (0.75), `docs/research_notes/10_rust_194_comprehensive_analysis.md` (0.75), `docs/research_notes/10_rust_194_research_update.md` (0.75) |
| `knowledge/06_ecosystem/emerging/05_rust_1_96.md` | Already redirects to concept | — |
| `docs/06_toolchain/06_19_rust_1_96_features.md` | Toolchain reference / panorama | vs `knowledge/06_ecosystem/emerging/05_rust_1_96.md` (0.78) |
| `docs/06_toolchain/06_22_rust_1_96_features.md` | Already redirects to concept | — |
| `docs/02_reference/quick_reference/02_rust_196_features_cheatsheet.md` | 1.96 cheat sheet | vs `knowledge/06_ecosystem/emerging/05_rust_1_96.md` (0.75) |
| `docs/06_toolchain/06_20_rustdoc_196_improvements.md` | Rustdoc 1.96 deep dive | Not compared (same dir) but duplicates `rustdoc_196_improvements.md` |
| `docs/06_toolchain/rustdoc_196_improvements.md` | Rustdoc 1.96 quick overview | Not compared (same dir) but duplicates `06_20...` |
| `docs/research_notes/10_rust_194_comprehensive_analysis.md` | 1.96 feature analysis (despite "194" name) | vs `concept/07_future/rust_1_96_stabilized.md` (0.75) |
| `docs/research_notes/10_rust_194_research_update.md` | 1.96 research update | vs `concept/07_future/rust_1_96_stabilized.md` (0.75) |

### 2.3 Rust 1.97

| File | Current role | Overlap pair from `PHASE0` |
|---|---|---|
| `concept/07_future/rust_1_97_preview.md` | **Project authority** for 1.97 preview | vs `docs/02_reference/quick_reference/02_rust_197_features_cheatsheet.md` (0.75) |
| `docs/06_toolchain/06_21_rust_1_97_features.md` | Pre-release stable-feature draft | vs `concept/07_future/rust_1_96_stabilized.md` (0.75), `knowledge/06_ecosystem/emerging/05_rust_1_96.md` (0.75) |
| `docs/02_reference/quick_reference/02_rust_197_features_cheatsheet.md` | 1.97 cheat sheet | vs `concept/07_future/rust_1_97_preview.md` (0.75) |

### 2.4 Rust Edition 2024

| File | Current role | Overlap pair from `PHASE0` |
|---|---|---|
| `concept/07_future/19_rust_edition_preview.md` | Designated authority (currently a 6-line redirect stub) | vs `knowledge/06_ecosystem/02_edition_2024.md` (0.75) |
| `concept/07_future/22_edition_guide.md` | Full Edition 2024 guide | vs `knowledge/06_ecosystem/02_edition_2024.md` (0.60) |
| `concept/07_future/23_rust_edition_guide.md` | Edition mechanism & migration guide | vs `knowledge/06_ecosystem/02_edition_2024.md` (0.60), `docs/research_notes/10_edition_guide_alignment.md` (0.60) |
| `knowledge/06_ecosystem/02_edition_2024.md` | Already redirects to `concept/07_future/19_rust_edition_preview.md` | — |
| `docs/research_notes/10_edition_guide_alignment.md` | Edition Guide alignment matrix | vs `concept/07_future/23_rust_edition_guide.md` (0.60) |

---

## 3. Consolidation Actions by Theme

### 3.1 Rust 1.95

| # | File | Target authoritative source | Action |
|---|---|---|---|
| 1 | **New** `concept/07_future/rust_1_95_stabilized.md` | Self | **Create** as the single 1.95 stable release index. Source content from `docs/02_reference/quick_reference/02_rust_195_features_cheatsheet.md` and the 1.95 sections of `concept/07_future/05_rust_version_tracking.md`. Link out to feature files (`if_let_guards`, `cfg_select!`, `range_types`, etc.). |
| 2 | `concept/07_future/05_rust_version_tracking.md` | Cross-version tracker | **Update** 1.95 section to link to new `rust_1_95_stabilized.md`; remove duplicated detail that now lives there. |
| 3 | `knowledge/06_ecosystem/emerging/03_rust_1_95.md` | `concept/07_future/rust_1_95_stabilized.md` | **Redirect** (replace content with redirect stub). |
| 4 | `knowledge/06_ecosystem/emerging/04_rust_1_95_preview.md` | Relevant feature previews (`18_async_drop_preview.md`, `15_gen_blocks_preview.md`, etc.) | **Redirect** to a new 1.95 preview landing or to the most relevant feature preview file. |
| 5 | `docs/06_toolchain/06_14_rust_1_95_nightly_preview.md` | `concept/07_future/rust_1_95_stabilized.md` + feature previews | **Convert** to a short toolchain-lens summary/redirect. Migrate stable 1.95 content to the new concept page; migrate nightly items to their feature-centric preview files. |
| 6 | `docs/02_reference/quick_reference/02_rust_195_features_cheatsheet.md` | `concept/07_future/rust_1_95_stabilized.md` | **Keep** as a quick-reference cheat sheet, but add a prominent "authoritative source" link and trim duplicated prose. |
| 7 | `knowledge/04_expert/safety_critical/01_mind_maps/03_rust_194_195_features_deep_dive.md` | `concept/07_future/rust_1_95_stabilized.md` | **Merge** unique safety-critical commentary into the 1.95 concept page or into `concept/06_ecosystem/safety_critical` files; then **archive/redirect**. |
| 8 | `docs/research_notes/10_rust_194_195_feature_matrix.md` | `concept/07_future/rust_1_95_stabilized.md` + `concept/07_future/rust_1_96_stabilized.md` | **Archive** with header + link. Migrate any unique formal definitions to the relevant concept page or `concept/04_formal/`. |

### 3.2 Rust 1.96

| # | File | Target authoritative source | 
