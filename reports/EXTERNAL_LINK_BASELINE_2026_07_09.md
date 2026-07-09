# External Link Health Baseline Report
>
> Generated: 2026-07-09
> Scanner: `scripts/i18n/check_external_links.py`
> Cache: `target/i18n_link_cache.json`

## Summary

- **Total external links scanned**: 4790
- **Healthy (200 OK, no redirect)**: 2043
- **Redirects (informational but actionable)**: 213
- **Failures / errors**: 97
- **Manual / whitelisted domains (skipped)**: 2437

## Failures by Status Code

- `404`: 70
- `ERR`: 16
- `503`: 4
- `405`: 3
- `429`: 1
- `418`: 1
- `500`: 1
- `502`: 1

## Top Offending Domains (Failures)

| Domain | Failures |
|---|---:|
| `doc.rust-lang.org` | 16 |
| `rust-lang.github.io` | 15 |
| `rustc-dev-guide.rust-lang.org` | 8 |
| `blog.rust-lang.org` | 4 |
| `wiki.haskell.org` | 4 |
| `cve.mitre.org` | 4 |
| `www.amazon.com` | 3 |
| `without.boats` | 3 |
| `bevyengine.org` | 3 |
| `www.st.com` | 3 |
| `downloads.haskell.org` | 2 |
| `releases.rs` | 2 |
| `actix.rs` | 2 |
| `www-kb.is.s.u-tokyo.ac.jp` | 1 |
| `www.cs.cornell.edu` | 1 |
| `bartoszmilewski.com` | 1 |
| `plv.mpi-sws.org` | 1 |
| `www.cambridge.org` | 1 |
| `www.haskell.org` | 1 |
| `learn.microsoft.com` | 1 |

## Top Whitelisted / Manual-Review Domains

| Domain | Skipped Links |
|---|---:|
| `github.com` | 658 |
| `docs.rs` | 555 |
| `en.wikipedia.org` | 397 |
| `doi.org` | 102 |
| `arxiv.org` | 51 |
| `dl.acm.org` | 47 |
| `rust-unofficial.github.io` | 42 |
| `crates.io` | 39 |
| `spec.ferrocene.dev` | 33 |
| `en.cppreference.com` | 27 |
| `rustwasm.github.io` | 22 |
| `nnethercote.github.io` | 19 |
| `model-checking.github.io` | 13 |
| `docs.aws.amazon.com` | 12 |
| `csrc.nist.gov` | 11 |
| `www.rabbitmq.com` | 11 |
| `google.github.io` | 10 |
| `developer.arm.com` | 10 |
| `www.iso.org` | 9 |
| `www.cs.cmu.edu` | 8 |

## First Batch: Actionable Links

| File | Original URL | Status | Suggested Replacement | Action |
|---|---|---|---|---|
| `concept\00_meta\00_framework\decidability_spectrum.md` | `https://blog.rust-lang.org/2023/06/01/` | `404` | `https://web.archive.org/web/*/https://blog.rust-lang.org/2023/06/01/` | replace |
| `concept\00_meta\00_framework\expressiveness_multiview.md` | `https://www-kb.is.s.u-tokyo.ac.jp/~koba/papers.html` | `404` | `https://web.archive.org/web/*/https://www-kb.is.s.u-tokyo.ac.jp/~koba/papers.html` | replace |
| `concept\00_meta\00_framework\expressiveness_multiview.md` | `https://www.cs.cornell.edu/~andru/papers/thesis.pdf` | `ERR([SSL: CERTIFICATE_VERIFY_FAILED] certificate verify failed: unable to get local issuer certificate (_ssl.c:1016))` | `ssl_issue@www.cs.cornell.edu` | manual_review |
| `concept\00_meta\00_framework\semantic_bridge_algorithms_patterns.md` | `https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/` | `429` | `rate_limited@bartoszmilewski.com` | whitelist |
| `concept\00_meta\02_sources\authority_source_map.md` | `https://wiki.haskell.org/Typeclassopedia` | `503` | `http_503@wiki.haskell.org` | manual_review |
| `concept\00_meta\02_sources\international_authority_index.md` | `https://rust-lang.github.io/rfcs/0000-safety-tags.html` | `404` | `https://rust-lang.github.io/rfcs/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/rfcs/0000-safety-tags.html` | manual_review |
| `concept\00_meta\02_sources\international_authority_index.md` | `https://wiki.haskell.org/` | `503` | `http_503@wiki.haskell.org` | manual_review |
| `concept\00_meta\04_navigation\self_assessment.md` | `https://rust-lang.github.io/rfcs/2394-async-await.html` | `404` | `https://rust-lang.github.io/rfcs/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/rfcs/2394-async-await.html` | manual_review |
| `concept\01_foundation\01_ownership_borrow_lifetime\01_ownership.md` | `https://plv.mpi-sws.org/semantics-of-memory-safety/` | `404` | `https://web.archive.org/web/*/https://plv.mpi-sws.org/semantics-of-memory-safety/` | replace |
| `concept\01_foundation\01_ownership_borrow_lifetime\02_borrowing.md` | `https://downloads.haskell.org/ghc/latest/docs/users_guide/libs.html` | `404` | `https://web.archive.org/web/*/https://downloads.haskell.org/ghc/latest/docs/users_guide/libs.html` | replace |
| `concept\01_foundation\01_ownership_borrow_lifetime\03_lifetimes.md` | `https://www.cambridge.org/core/books/introduction-to-lattices-and-order/` | `404` | `https://web.archive.org/web/*/https://www.cambridge.org/core/books/introduction-to-lattices-and-order/` | replace |
| `concept\01_foundation\02_type_system\04_type_system.md` | `https://www.haskell.org/definition/haskell2010/` | `404` | `https://web.archive.org/web/*/https://www.haskell.org/definition/haskell2010/` | replace |
| `concept\01_foundation\07_modules_and_items\43_type_aliases.md` | `https://doc.rust-lang.org/rust-by-example/custom_types/alias.html` | `404` | `https://doc.rust-lang.org/rust-by-example/custom_types/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/rust-by-example/custom_types/alias.html` | manual_review |
| `concept\02_intermediate\README.md` | `https://learn.microsoft.com/en-us/training/paths/rust/` | `ERR(_ssl.c:999: The handshake operation timed out)` | `timeout@learn.microsoft.com` | manual_review |
| `concept\02_intermediate\01_generics\02_generics.md` | `https://wiki.haskell.org/Type_families` | `503` | `http_503@wiki.haskell.org` | manual_review |
| `concept\02_intermediate\03_error_handling\04_error_handling.md` | `https://rustc-dev-guide.rust-lang.org/codegen/implicit-caller-location.html` | `404` | `https://web.archive.org/web/*/https://rustc-dev-guide.rust-lang.org/codegen/implicit-caller-location.html` | replace |
| `concept\02_intermediate\03_error_handling\04_error_handling.md` | `https://doc.rust-lang.org/std/panic/struct.PanicInfo.html` | `404` | `https://doc.rust-lang.org/std/panic/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/std/panic/struct.PanicInfo.html` | manual_review |
| `concept\02_intermediate\04_types_and_conversions\35_unions.md` | `https://doc.rust-lang.org/nomicon/unions.html` | `404` | `https://doc.rust-lang.org/nomicon/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/nomicon/unions.html` | manual_review |
| `concept\02_intermediate\04_types_and_conversions\35_unions.md` | `https://rust-lang.github.io/unsafe-code-guidelines/reference/types/union.html` | `404` | `https://rust-lang.github.io/unsafe-code-guidelines/reference/types/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/unsafe-code-guidelines/reference/types/union.html` | manual_review |
| `concept\02_intermediate\04_types_and_conversions\37_type_conversions.md` | `https://doc.rust-lang.org/reference/expressions/cast-expr.html` | `404` | `https://doc.rust-lang.org/reference/expressions/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/reference/expressions/cast-expr.html` | manual_review |
| `concept\03_advanced\00_concurrency\01_concurrency.md` | `https://downloads.haskell.org/ghc/latest/docs/users_guide/parallel.html` | `404` | `https://web.archive.org/web/*/https://downloads.haskell.org/ghc/latest/docs/users_guide/parallel.html` | replace |
| `concept\03_advanced\00_concurrency\16_lock_free.md` | `https://www.amazon.com/Art-Multiprocessor-Programming-Revised-Reprint/dp/0123973376` | `405` | `http_405@www.amazon.com` | manual_review |
| `concept\03_advanced\01_async\02_async.md` | `https://doc.rust-lang.org/book/ch17-02-async-fn-and-messages.html` | `404` | `https://doc.rust-lang.org/book/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/book/ch17-02-async-fn-and-messages.html` | manual_review |
| `concept\03_advanced\01_async\02_async.md` | `https://doc.rust-lang.org/book/ch17-04-pin.html` | `404` | `https://doc.rust-lang.org/book/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/book/ch17-04-pin.html` | manual_review |
| `concept\03_advanced\01_async\02_async.md` | `https://doc.rust-lang.org/book/ch17-05-concurrency.html` | `404` | `https://doc.rust-lang.org/book/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/book/ch17-05-concurrency.html` | manual_review |
| `concept\03_advanced\01_async\02_async.md` | `https://without.boats/blog/pin-and-suffering/` | `404` | `https://web.archive.org/web/*/https://without.boats/blog/pin-and-suffering/` | replace |
| `concept\03_advanced\01_async\02_async.md` | `https://without.boats/blog/the-cost-of-dynamic-dispatch/` | `404` | `https://web.archive.org/web/*/https://without.boats/blog/the-cost-of-dynamic-dispatch/` | replace |
| `concept\03_advanced\01_async\39_future_and_executor_mechanisms.md` | `https://rust-lang.github.io/async-book/04_pinning/01_chapter.html` | `404` | `https://rust-lang.github.io/async-book/04_pinning/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/async-book/04_pinning/01_chapter.html` | manual_review |
| `concept\03_advanced\02_unsafe\03_unsafe.md` | `https://llvm.org/docs/SanitizerCoverage.html` | `404` | `https://web.archive.org/web/*/https://llvm.org/docs/SanitizerCoverage.html` | replace |
| `concept\03_advanced\07_unsafe_internals\37_unsafe_collections_internals.md` | `https://doc.rust-lang.org/nomicon/arc-mutex.html` | `404` | `https://doc.rust-lang.org/nomicon/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/nomicon/arc-mutex.html` | manual_review |
| `concept\03_advanced\07_unsafe_internals\37_unsafe_collections_internals.md` | `https://rust-lang.github.io/unsafe-code-guidelines/reference/types/reference.html` | `404` | `https://rust-lang.github.io/unsafe-code-guidelines/reference/types/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/unsafe-code-guidelines/reference/types/reference.html` | manual_review |
| `concept\04_formal\00_type_theory\10_category_theory.md` | `https://wiki.haskell.org/Functor` | `503` | `http_503@wiki.haskell.org` | manual_review |
| `concept\04_formal\00_type_theory\27_type_checking_and_inference.md` | `https://rustc-dev-guide.rust-lang.org/type-checking.html` | `404` | `https://web.archive.org/web/*/https://rustc-dev-guide.rust-lang.org/type-checking.html` | replace |
| `concept\04_formal\02_separation_logic\04_rustbelt.md` | `https://popl.sigplan.org/` | `ERR([SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016))` | `ssl_issue@popl.sigplan.org` | manual_review |
| `concept\04_formal\03_operational_semantics\18_evaluation_strategies.md` | `https://www.amazon.com/Lambda-Calculus-Its-Syntax-Studies/dp/0444875085` | `405` | `http_405@www.amazon.com` | manual_review |
| `concept\04_formal\04_model_checking\05_verification_toolchain.md` | `https://rust-lang.github.io/rust-project-goals/2024h2/formal-methods.html` | `404` | `https://rust-lang.github.io/rust-project-goals/2024h2/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/rust-project-goals/2024h2/formal-methods.html` | manual_review |
| `concept\04_formal\05_rustc_internals\53_generics_compiler_behavior.md` | `https://doc.rust-lang.org/nomicon/trait-objects.html` | `404` | `https://doc.rust-lang.org/nomicon/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/nomicon/trait-objects.html` | manual_review |
| `concept\05_comparative\README.md` | `https://ieeexplore.ieee.org/` | `418` | `http_418@ieeexplore.ieee.org` | manual_review |
| `concept\05_comparative\00_paradigms\05_execution_model_isomorphism.md` | `https://go.dev/wiki/ConcurrencyPatterns` | `404` | `https://web.archive.org/web/*/https://go.dev/wiki/ConcurrencyPatterns` | replace |
| `concept\05_comparative\00_paradigms\05_execution_model_isomorphism.md` | `https://tokio.rs/tokio/topics/runtime` | `404` | `https://web.archive.org/web/*/https://tokio.rs/tokio/topics/runtime` | replace |
| `concept\06_ecosystem\00_toolchain\67_llvm_backend_and_codegen.md` | `https://rustc-dev-guide.rust-lang.org/backend/backend.html` | `404` | `https://web.archive.org/web/*/https://rustc-dev-guide.rust-lang.org/backend/backend.html` | replace |
| `concept\06_ecosystem\00_toolchain\67_llvm_backend_and_codegen.md` | `https://rustc-dev-guide.rust-lang.org/backend/mono.html` | `404` | `https://web.archive.org/web/*/https://rustc-dev-guide.rust-lang.org/backend/mono.html` | replace |
| `concept\06_ecosystem\00_toolchain\68_rustc_driver_and_stable_mir.md` | `https://rustc-dev-guide.rust-lang.org/rustc-driver.html` | `404` | `https://web.archive.org/web/*/https://rustc-dev-guide.rust-lang.org/rustc-driver.html` | replace |
| `concept\06_ecosystem\00_toolchain\69_compiler_diagnostics_and_ui_tests.md` | `https://rustc-dev-guide.rust-lang.org/diagnostics/lint-guidelines.html` | `404` | `https://web.archive.org/web/*/https://rustc-dev-guide.rust-lang.org/diagnostics/lint-guidelines.html` | replace |
| `concept\06_ecosystem\00_toolchain\70_rustc_bootstrap.md` | `https://rustc-dev-guide.rust-lang.org/building/bootstrapping.html` | `404` | `https://web.archive.org/web/*/https://rustc-dev-guide.rust-lang.org/building/bootstrapping.html` | replace |
| `concept\06_ecosystem\00_toolchain\71_compiler_testing.md` | `https://rustc-dev-guide.rust-lang.org/tests/profiling.html` | `404` | `https://web.archive.org/web/*/https://rustc-dev-guide.rust-lang.org/tests/profiling.html` | replace |
| `concept\06_ecosystem\01_cargo\61_cargo_source_replacement.md` | `https://doc.rust-lang.org/cargo/reference/commands/cargo-vendor.html` | `404` | `https://doc.rust-lang.org/cargo/reference/commands/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/cargo/reference/commands/cargo-vendor.html` | manual_review |
| `concept\06_ecosystem\01_cargo\62_cargo_registries_and_publishing.md` | `https://doc.rust-lang.org/cargo/reference/authentication.html` | `404` | `https://doc.rust-lang.org/cargo/reference/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/cargo/reference/authentication.html` | manual_review |
| `concept\06_ecosystem\01_cargo\87_build_std.md` | `https://docs.rust-embedded.org/embedonomicon/build-std.html` | `404` | `https://web.archive.org/web/*/https://docs.rust-embedded.org/embedonomicon/build-std.html` | replace |
| `concept\06_ecosystem\03_design_patterns\05_system_design_principles.md` | `https://www.stroustrup.com/de.html` | `404` | `https://web.archive.org/web/*/https://www.stroustrup.com/de.html` | replace |
| `concept\06_ecosystem\03_design_patterns\34_idioms_spectrum.md` | `https://bevyengine.org/learn/book/ecs/` | `404` | `https://web.archive.org/web/*/https://bevyengine.org/learn/book/ecs/` | replace |
| `concept\06_ecosystem\03_design_patterns\41_workflow_theory.md` | `https://www.amazon.com/Communicating-Mobile-Systems-Calculus-Cambridge/dp/0521658691` | `405` | `http_405@www.amazon.com` | manual_review |
| `concept\06_ecosystem\04_web_and_networking\38_network_protocols.md` | `https://doc.rust-lang.org/rust-by-example/std_misc/net.html` | `404` | `https://doc.rust-lang.org/rust-by-example/std_misc/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/rust-by-example/std_misc/net.html` | manual_review |
| `concept\06_ecosystem\05_systems_and_embedded\08_wasi.md` | `https://doc.rust-lang.org/reference/ownership.html` | `404` | `https://doc.rust-lang.org/reference/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/reference/ownership.html` | manual_review |
| `concept\06_ecosystem\05_systems_and_embedded\39_os_kernel.md` | `https://www.usenix.org/conference/osdi20/presentation/raman` | `404` | `https://web.archive.org/web/*/https://www.usenix.org/conference/osdi20/presentation/raman` | replace |
| `concept\06_ecosystem\05_systems_and_embedded\52_robotics.md` | `https://www.eprosima.com/index.php/products-all/eprosima-fast-dds` | `ERR(TimeoutError('The read operation timed out'))` | `timeout@www.eprosima.com` | manual_review |
| `concept\06_ecosystem\05_systems_and_embedded\53_embedded_graphics.md` | `https://www.st.com/resource/en/reference_manual/rm0090-stm32f405415-stm32f407417-stm32f427437-and-stm32f429439-advanced-armbased-32bit-mcus-stmicroelectronics.pdf` | `ERR(TimeoutError('The read operation timed out'))` | `timeout@www.st.com` | manual_review |
| `concept\06_ecosystem\05_systems_and_embedded\53_embedded_graphics.md` | `https://www.st.com/resource/en/application_note/an4031-using-the-stm32f2-stm32f4-and-stm32f7-series-dma-controllers-stmicroelectronics.pdf` | `ERR(TimeoutError('The read operation timed out'))` | `timeout@www.st.com` | manual_review |
| `concept\06_ecosystem\05_systems_and_embedded\53_embedded_graphics.md` | `https://www.st.com/` | `ERR(TimeoutError('The read operation timed out'))` | `timeout@www.st.com` | manual_review |
| `concept\06_ecosystem\06_data_and_distributed\04_application_domains.md` | `https://rust-lang.github.io/rust-project-goals/2025h1/Rust-for-Linux.html` | `404` | `https://rust-lang.github.io/rust-project-goals/2025h1/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/rust-project-goals/2025h1/Rust-for-Linux.html` | manual_review |
| `concept\06_ecosystem\06_data_and_distributed\36_stream_processing_ecosystem.md` | `https://www.fluvio.io/blog/` | `404` | `https://web.archive.org/web/*/https://www.fluvio.io/blog/` | replace |
| `concept\06_ecosystem\06_data_and_distributed\50_distributed_consensus.md` | `https://algodist.labri.fr/index.php/Main/GT` | `ERR([SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016))` | `ssl_issue@algodist.labri.fr` | manual_review |
| `concept\06_ecosystem\07_security_and_cryptography\19_security_practices.md` | `https://cve.mitre.org/cgi-bin/cvekey.cgi?keyword=rust` | `ERR([SSL: CERTIFICATE_VERIFY_FAILED] certificate verify failed: certificate has expired (_ssl.c:1016))` | `ssl_issue@cve.mitre.org` | manual_review |
| `concept\06_ecosystem\08_formal_verification\74_formal_verification_tools.md` | `https://hal.inria.fr/hal-03737818` | `500` | `http_500@hal.inria.fr` | manual_review |
| `concept\06_ecosystem\11_domain_applications\06_blockchain.md` | `https://www.coindesk.com/learn/the-dao-attack-that-changed-ethereum/` | `404` | `https://web.archive.org/web/*/https://www.coindesk.com/learn/the-dao-attack-that-changed-ethereum/` | replace |
| `concept\07_future\00_version_tracking\05_rust_version_tracking.md` | `https://cve.mitre.org/cgi-bin/cvename.cgi?name=CVE-2026-31431` | `ERR([SSL: CERTIFICATE_VERIFY_FAILED] certificate verify failed: certificate has expired (_ssl.c:1016))` | `ssl_issue@cve.mitre.org` | manual_review |
| `concept\07_future\03_preview_features\04_effects_system.md` | `https://rust-lang.github.io/keyword-generics-initiative/updates/2024-02-09-extending-rusts-effect-system.html` | `404` | `https://rust-lang.github.io/keyword-generics-initiative/updates/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/keyword-generics-initiative/updates/2024-02-09-extending-rusts-effect-system.html` | manual_review |
| `concept\07_future\03_preview_features\04_effects_system.md` | `https://blog.rust-lang.org/inside-rust/2023/02/23/keyword-generics-progress-report.html` | `404` | `https://web.archive.org/web/*/https://blog.rust-lang.org/inside-rust/2023/02/23/keyword-generics-progress-report.html` | replace |
| `concept\07_future\03_preview_features\04_effects_system.md` | `https://rust-lang.github.io/rust-project-goals/2025h1/const-traits.html` | `404` | `https://rust-lang.github.io/rust-project-goals/2025h1/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/rust-project-goals/2025h1/const-traits.html` | manual_review |
| `concept\07_future\03_preview_features\04_effects_system.md` | `https://rust-lang.github.io/keyword-generics-initiative/` | `404` | `https://rust-lang.github.io/keyword-generics-initiative/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/keyword-generics-initiative/` | manual_review |
| `concept\07_future\04_research_and_experimental\01_ai_integration.md` | `https://arewelearningyet.com/` | `ERR([SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016))` | `ssl_issue@arewelearningyet.com` | manual_review |
| `concept\07_future\04_research_and_experimental\03_evolution.md` | `https://www.rust-lang.org/policies/roadmap` | `404` | `https://web.archive.org/web/*/https://www.rust-lang.org/policies/roadmap` | replace |
| `concept\07_future\04_research_and_experimental\03_evolution.md` | `https://without.boats/blog/the-rust-i-wanted-had-no-future/` | `404` | `https://web.archive.org/web/*/https://without.boats/blog/the-rust-i-wanted-had-no-future/` | replace |
| `knowledge\00_start\04_rust_philosophy.md` | `https://blog.rust-lang.org/2017/` | `404` | `https://web.archive.org/web/*/https://blog.rust-lang.org/2017/` | replace |
| `knowledge\01_fundamentals\02_iterators.md` | `https://releases.rs/docs/1.94/` | `404` | `https://web.archive.org/web/*/https://releases.rs/docs/1.94/` | replace |
| `knowledge\02_intermediate\control_flow\02_let_chains.md` | `https://rust-lang.github.io/rfcs/2497.html` | `404` | `https://rust-lang.github.io/rfcs/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/rfcs/2497.html` | manual_review |
| `knowledge\02_intermediate\control_flow\02_let_chains.md` | `https://blog.rust-lang.org/2022/` | `404` | `https://web.archive.org/web/*/https://blog.rust-lang.org/2022/` | replace |
| `knowledge\02_intermediate\macros\01_cfg_select.md` | `https://releases.rs/docs/1.95/` | `404` | `https://web.archive.org/web/*/https://releases.rs/docs/1.95/` | replace |
| `knowledge\03_advanced\04_lazy_initialization.md` | `https://rust-lang.github.io/rfcs/2788.html` | `404` | `https://rust-lang.github.io/rfcs/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/rfcs/2788.html` | manual_review |
| `knowledge\03_advanced\06_type_driven_correctness.md` | `https://rust-lang.github.io/rfcs/1228.html` | `404` | `https://rust-lang.github.io/rfcs/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/rfcs/1228.html` | manual_review |
| `knowledge\03_advanced\unsafe\03_maybe_uninit.md` | `https://rust-lang.github.io/rfcs/1892.html` | `404` | `https://rust-lang.github.io/rfcs/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/rfcs/1892.html` | manual_review |
| `knowledge\04_expert\02_unsafe_audit.md` | `https://rust-lang.github.io/rfcs/2585.html` | `404` | `https://rust-lang.github.io/rfcs/ 或 https://web.archive.org/web/*/https://rust-lang.github.io/rfcs/2585.html` | manual_review |
| `knowledge\04_expert\safety_critical\03_readme_rust_safety_critical_ecosystem.md` | `https://plr.csail.mit.edu` | `ERR([SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016))` | `ssl_issue@plr.csail.mit.edu` | manual_review |
| `docs\10_2026_rust_ecosystem_comprehensive_review_with_citations.md` | `https://cve.mitre.org/` | `ERR([SSL: CERTIFICATE_VERIFY_FAILED] certificate verify failed: certificate has expired (_ssl.c:1016))` | `ssl_issue@cve.mitre.org` | manual_review |
| `docs\10_2026_rust_ecosystem_comprehensive_review_with_citations.md` | `https://cve.mitre.org/cgi-bin/cvename.cgi?name=CVE-2025-68260` | `ERR([SSL: CERTIFICATE_VERIFY_FAILED] certificate verify failed: certificate has expired (_ssl.c:1016))` | `ssl_issue@cve.mitre.org` | manual_review |
| `docs\01_learning\learning_mvp_path.md` | `https://doc.rust-lang.org/book/ch10-00-generic-types-traits-and-lifetimes.html` | `404` | `https://doc.rust-lang.org/book/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/book/ch10-00-generic-types-traits-and-lifetimes.html` | manual_review |
| `docs\01_learning\learning_mvp_path.md` | `https://doc.rust-lang.org/book/ch21-00-final-project.html` | `404` | `https://doc.rust-lang.org/book/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/book/ch21-00-final-project.html` | manual_review |
| `docs\04_research\04_safety_critical_alignment_2026.md` | `https://www.rtca.org/product/307` | `404` | `https://web.archive.org/web/*/https://www.rtca.org/product/307` | replace |
| `docs\research_notes\10_authoritative_alignment_gap_matrix.md` | `https://www.pearson.com/en-us/subject-catalog/p/software-architecture-in-practice/P200000005792` | `502` | `http_502@www.pearson.com` | manual_review |
| `docs\research_notes\10_changelog.md` | `https://keepachangelog.com/zh-CN/1.0.0/` | `ERR(TimeoutError('The read operation timed out'))` | `timeout@keepachangelog.com` | manual_review |
| `docs\research_notes\formal_methods\10_testing_strategy_decision_tree.md` | `https://pldi.sigplan.org/` | `ERR([SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016))` | `ssl_issue@pldi.sigplan.org` | manual_review |
| `docs\research_notes\software_design_theory\07_crate_architectures\05_bevy_architecture.md` | `https://bevyengine.org/learn/book/states/` | `404` | `https://web.archive.org/web/*/https://bevyengine.org/learn/book/states/` | replace |
| `docs\research_notes\software_design_theory\07_crate_architectures\05_bevy_architecture.md` | `https://bevyengine.org/learn/book/resources/` | `404` | `https://web.archive.org/web/*/https://bevyengine.org/learn/book/resources/` | replace |
| `docs\research_notes\software_design_theory\07_crate_architectures\12_actix_web_architecture.md` | `https://actix.rs/actors/` | `404` | `https://web.archive.org/web/*/https://actix.rs/actors/` | replace |
| `docs\research_notes\software_design_theory\07_crate_architectures\12_actix_web_architecture.md` | `https://actix.rs/docs/architecture` | `404` | `https://web.archive.org/web/*/https://actix.rs/docs/architecture` | replace |
| `docs\research_notes\software_design_theory\07_crate_architectures\19_crossbeam_architecture.md` | `https://www.cs.brown.edu/~mph/HerlihyShavit/` | `404` | `https://web.archive.org/web/*/https://www.cs.brown.edu/~mph/HerlihyShavit/` | replace |
| `docs\research_notes\software_design_theory\07_crate_architectures\19_crossbeam_architecture.md` | `https://doc.rust-lang.org/std/ync.html` | `404` | `https://doc.rust-lang.org/std/ 或 https://web.archive.org/web/*/https://doc.rust-lang.org/std/ync.html` | manual_review |
| `concept\00_meta\00_framework\03_bloom_taxonomy.md` | `https://cft.vanderbilt.edu/guides-sub-pages/blooms-taxonomy/` | `200` | `https://www.vanderbilt.edu/advanced-institute/` | replace |
| `concept\00_meta\00_framework\03_bloom_taxonomy.md` | `https://www.rust-lang.org/learn` | `200` | `https://rust-lang.org/learn/` | replace |
| `concept\00_meta\00_framework\fault_tree_analysis_collection.md` | `https://doc.rust-lang.org/` | `200` | `https://doc.rust-lang.org/stable/` | replace |

## Domains Recommended for Whitelist

The following domains returned timeouts, rate-limits, SSL errors, or bot blocks during this run. Consider adding them to `MANUAL_DOMAINS` in `scripts/i18n/check_external_links.py` if they persist.

- `wiki.haskell.org` (4 occurrences)
- `cve.mitre.org` (4 occurrences)
- `www.amazon.com` (3 occurrences)
- `www.st.com` (3 occurrences)
- `www.cs.cornell.edu` (1 occurrence)
- `bartoszmilewski.com` (1 occurrence)
- `learn.microsoft.com` (1 occurrence)
- `popl.sigplan.org` (1 occurrence)
- `ieeexplore.ieee.org` (1 occurrence)
- `www.eprosima.com` (1 occurrence)
- `algodist.labri.fr` (1 occurrence)
- `arewelearningyet.com` (1 occurrence)
- `plr.csail.mit.edu` (1 occurrence)
- `www.pearson.com` (1 occurrence)
- `keepachangelog.com` (1 occurrence)
- `pldi.sigplan.org` (1 occurrence)

## Notes

- Redirects are listed as `replace` because the server returned a permanent/temporary redirect target.
- `archive.org` suggestions point to the Wayback Machine capture list for the original URL.
- `manual_review` items need human verification (e.g., expired certificate, timeout, ambiguous redirect).
- No Markdown files were modified during this audit.
