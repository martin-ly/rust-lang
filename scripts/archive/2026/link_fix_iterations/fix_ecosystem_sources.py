#!/usr/bin/env python3
"""将 06_ecosystem 中仍使用根 URL 的概念文件来源替换为更具体的权威链接."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"

ECOSYSTEM_SOURCES = {
    "06_ecosystem/02_patterns.md": "[Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) · [TRPL — Patterns](https://doc.rust-lang.org/book/ch18-00-patterns.html) · [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)",
    "06_ecosystem/03_idioms_spectrum.md": "[Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) · [Rust By Example](https://doc.rust-lang.org/rust-by-example/) · [Rust Reference](https://doc.rust-lang.org/reference/)",
    "06_ecosystem/04_application_domains.md": "[TRPL](https://doc.rust-lang.org/book/) · [Cargo Book](https://doc.rust-lang.org/cargo/) · [crates.io](https://crates.io/)",
    "06_ecosystem/05_system_design_principles.md": "[Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) · [TRPL — Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html) · [Cargo Book](https://doc.rust-lang.org/cargo/)",
    "06_ecosystem/08_wasi.md": "[WASI](https://wasi.dev/) · [Rust and WebAssembly Book](https://rustwasm.github.io/book/) · [Rust Platform Support](https://doc.rust-lang.org/rustc/platform-support.html)",
    "06_ecosystem/13_logging_observability.md": "[log crate](https://docs.rs/log/) · [tracing](https://docs.rs/tracing/) · [std::fmt](https://doc.rust-lang.org/std/fmt/)",
    "06_ecosystem/17_cross_compilation.md": "[rustup Cross-compilation](https://rust-lang.github.io/rustup/cross-compilation.html) · [Platform Support](https://doc.rust-lang.org/rustc/platform-support.html) · [Cargo — Configuration](https://doc.rust-lang.org/cargo/reference/config.html)",
    "06_ecosystem/18_distributed_systems.md": "[tokio](https://docs.rs/tokio/) · [tower](https://docs.rs/tower/) · [tonic](https://docs.rs/tonic/)",
    "06_ecosystem/19_security_practices.md": "[Rust Secure Code WG](https://rust-secure-code.github.io/) · [Cargo — Specifying Dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) · [Rustonomicon](https://doc.rust-lang.org/nomicon/)",
    "06_ecosystem/20_licensing_and_compliance.md": "[Cargo — Manifest: license](https://doc.rust-lang.org/cargo/reference/manifest.html#the-license-and-license-file-fields) · [Choose a License](https://choosealicense.com/)",
    "06_ecosystem/21_game_development.md": "[Bevy Engine](https://bevyengine.org/) · [wgpu](https://docs.rs/wgpu/)",
    "06_ecosystem/22_embedded_systems.md": "[The Embedded Rust Book](https://docs.rust-embedded.org/book/) · [Embedded Rust Working Group](https://github.com/rust-embedded/wg)",
    "06_ecosystem/23_database_access.md": "[Diesel](https://docs.rs/diesel/) · [SQLx](https://docs.rs/sqlx/) · [tokio-postgres](https://docs.rs/tokio-postgres/)",
    "06_ecosystem/24_cloud_native.md": "[tokio](https://docs.rs/tokio/) · [kube-rs](https://docs.rs/kube/) · [Cargo Book](https://doc.rust-lang.org/cargo/)",
    "06_ecosystem/25_cli_development.md": "[Rust CLI Book](https://rust-cli.github.io/book/) · [clap](https://docs.rs/clap/) · [Cargo Book](https://doc.rust-lang.org/cargo/)",
    "06_ecosystem/26_game_development.md": "[Bevy Engine](https://bevyengine.org/) · [wgpu](https://docs.rs/wgpu/)",
    "06_ecosystem/27_web_frameworks.md": "[axum](https://docs.rs/axum/) · [actix-web](https://docs.rs/actix-web/) · [Rocket](https://rocket.rs/)",
    "06_ecosystem/28_devops_and_ci_cd.md": "[GitHub Actions Docs](https://docs.github.com/en/actions) · [Cargo Book](https://doc.rust-lang.org/cargo/)",
    "06_ecosystem/29_algorithms_competitive_programming.md": "[std::collections](https://doc.rust-lang.org/std/collections/) · [Rust By Example](https://doc.rust-lang.org/rust-by-example/) · [The Algorithms — Rust](https://github.com/TheAlgorithms/Rust)",
    "06_ecosystem/30_system_composability.md": "[tokio](https://docs.rs/tokio/) · [tower](https://docs.rs/tower/) · [rayon](https://docs.rs/rayon/)",
    "06_ecosystem/31_microservice_patterns.md": "[tower](https://docs.rs/tower/) · [tonic](https://docs.rs/tonic/) · [failsafe](https://docs.rs/failsafe/)",
    "06_ecosystem/32_event_driven_architecture.md": "[tokio](https://docs.rs/tokio/) · [lapin](https://docs.rs/lapin/) · [rdkafka](https://docs.rs/rdkafka/)",
    "06_ecosystem/33_cqrs_event_sourcing.md": "[eventstore-rs](https://docs.rs/eventstore/) · [cqrs-es](https://docs.rs/cqrs-es/)",
    "06_ecosystem/35_architecture_patterns.md": "[Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) · [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)",
    "06_ecosystem/35_pattern_composition_algebra.md": "[Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) · [Category Theory for Programmers](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/)",
    "06_ecosystem/36_stream_processing_ecosystem.md": "[tokio-stream](https://docs.rs/tokio-stream/) · [futures](https://docs.rs/futures/) · [fluvio](https://docs.rs/fluvio/)",
    "06_ecosystem/37_database_systems.md": "[Diesel](https://docs.rs/diesel/) · [SQLx](https://docs.rs/sqlx/) · [TiKV](https://tikv.org/)",
    "06_ecosystem/38_network_protocols.md": "[tokio](https://docs.rs/tokio/) · [quinn](https://docs.rs/quinn/) · [rustls](https://docs.rs/rustls/)",
    "06_ecosystem/39_os_kernel.md": "[Rust for Linux](https://rust-for-linux.com/) · [Redox OS](https://www.redox-os.org/) · [Rustonomicon](https://doc.rust-lang.org/nomicon/)",
    "06_ecosystem/40_reactive_programming.md": "[futures](https://docs.rs/futures/) · [tokio](https://docs.rs/tokio/) · [rxrust](https://docs.rs/rxrust/)",
    "06_ecosystem/41_workflow_theory.md": "[Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) · [Cargo Book](https://doc.rust-lang.org/cargo/)",
    "06_ecosystem/42_api_design_patterns.md": "[Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) · [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)",
    "06_ecosystem/43_security_cryptography.md": "[ring](https://docs.rs/ring/) · [rustls](https://docs.rs/rustls/) · [Rust Crypto](https://github.com/RustCrypto)",
    "06_ecosystem/45_compiler_internals.md": "[Rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/) · [Rust Reference](https://doc.rust-lang.org/reference/)",
    "06_ecosystem/46_machine_learning_ecosystem.md": "[candle](https://docs.rs/candle-core/) · [burn](https://docs.rs/burn/) · [tch-rs](https://docs.rs/tch/)",
    "06_ecosystem/47_compiler_infrastructure.md": "[Rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/) · [rustc_driver](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_driver/)",
    "06_ecosystem/47_formal_verification_tools.md": "[Kani](https://model-checking.github.io/kani/) · [Creusot](https://creusot.rs/) · [Verus](https://verus-lang.github.io/verus/)",
    "06_ecosystem/48_data_engineering.md": "[polars](https://docs.rs/polars/) · [arrow-rs](https://docs.rs/arrow/) · [datafusion](https://docs.rs/datafusion/)",
    "06_ecosystem/48_industrial_case_studies.md": "[Rust in Production](https://www.rust-lang.org/) · [Rust Foundation](https://foundation.rust-lang.org/)",
    "06_ecosystem/49_game_engine_internals.md": "[Bevy Engine](https://bevyengine.org/) · [wgpu](https://docs.rs/wgpu/)",
    "06_ecosystem/50_distributed_consensus.md": "[raft-rs](https://docs.rs/raft/) · [hotstuff-rs](https://docs.rs/hotstuff-rs/)",
    "06_ecosystem/52_robotics.md": "[rclrs](https://docs.rs/rclrs/) · [ROS2 Rust](https://github.com/ros2-rust/ros2_rust)",
    "06_ecosystem/53_embedded_graphics.md": "[embedded-graphics](https://docs.rs/embedded-graphics/) · [lvgl-rs](https://docs.rs/lvgl/)",
    "06_ecosystem/54_webassembly_advanced.md": "[Rust and WebAssembly Book](https://rustwasm.github.io/book/) · [wasm-bindgen](https://docs.rs/wasm-bindgen/) · [Wasmtime Rust API](https://docs.wasmtime.dev/lang-rust.html)",
    "06_ecosystem/55_rust_for_data_science.md": "[polars](https://docs.rs/polars/) · [ndarray](https://docs.rs/ndarray/) · [plotters](https://docs.rs/plotters/)",
    "06_ecosystem/56_c_to_rust_translation.md": "[Rustonomicon — FFI](https://doc.rust-lang.org/nomicon/ffi.html) · [bindgen](https://docs.rs/bindgen/)",
    "06_ecosystem/57_quiz_toolchain.md": "[Cargo Book](https://doc.rust-lang.org/cargo/) · [rustup](https://rust-lang.github.io/rustup/)",
    "06_ecosystem/58_platform_rust_integration.md": "[Android Rust](https://source.android.com/docs/core/architecture/rust) · [Chromium Rust](https://www.chromium.org/developers/design-documents/rust/) · [Rust for Linux](https://rust-for-linux.com/)",
    "06_ecosystem/59_cargo_build_scripts.md": "[Cargo — Build Scripts](https://doc.rust-lang.org/cargo/reference/build-scripts.html)",
    "06_ecosystem/60_cargo_dependency_resolution.md": "[Cargo — Dependency Resolution](https://doc.rust-lang.org/cargo/reference/resolver.html)",
    "06_ecosystem/61_cargo_source_replacement.md": "[Cargo — Source Replacement](https://doc.rust-lang.org/cargo/reference/source-replacement.html)",
    "06_ecosystem/62_cargo_registries_and_publishing.md": "[Cargo — Registries](https://doc.rust-lang.org/cargo/reference/registries.html)",
    "06_ecosystem/63_cargo_authentication_and_cache.md": "[Cargo — Registry Authentication](https://doc.rust-lang.org/cargo/reference/registry-authentication.html) · [Cargo — Configuration](https://doc.rust-lang.org/cargo/reference/config.html)",
    "06_ecosystem/64_cargo_manifest_reference.md": "[Cargo — Manifest Format](https://doc.rust-lang.org/cargo/reference/manifest.html)",
    "06_ecosystem/65_cargo_profiles_and_lints.md": "[Cargo — Profiles](https://doc.rust-lang.org/cargo/reference/profiles.html) · [Cargo — Lints](https://doc.rust-lang.org/cargo/reference/manifest.html#the-lints-table)",
    "06_ecosystem/66_cargo_subcommands_and_plugins.md": "[Cargo — External Tools](https://doc.rust-lang.org/cargo/reference/external-tools.html) · [Cargo — Commands](https://doc.rust-lang.org/cargo/reference/commands/index.html)",
    "06_ecosystem/67_llvm_backend_and_codegen.md": "[Rustc Dev Guide — Backend](https://rustc-dev-guide.rust-lang.org/backend/index.html) · [LLVM Documentation](https://llvm.org/docs/)",
    "06_ecosystem/68_rustc_driver_and_stable_mir.md": "[Rustc Dev Guide — rustc_driver](https://rustc-dev-guide.rust-lang.org/rustc-driver.html) · [Stable MIR](https://rust-lang.github.io/stable-mir/)",
    "06_ecosystem/69_compiler_diagnostics_and_ui_tests.md": "[Rustc Dev Guide — Diagnostics](https://rustc-dev-guide.rust-lang.org/diagnostics.html) · [compiletest](https://rustc-dev-guide.rust-lang.org/tests/compiletest.html)",
    "06_ecosystem/70_rustc_bootstrap.md": "[Rustc Dev Guide — Bootstrapping](https://rustc-dev-guide.rust-lang.org/building/bootstrapping.html)",
    "06_ecosystem/71_compiler_testing.md": "[Rustc Dev Guide — Testing](https://rustc-dev-guide.rust-lang.org/tests/index.html)",
}


def main():
    for rel, links in ECOSYSTEM_SOURCES.items():
        path = ROOT / rel
        if not path.exists():
            print(f"skip (missing): {rel}")
            continue
        text = path.read_text(encoding="utf-8")
        new_text, n = re.subn(
            r'^>\s*\*\*来源\*\*:\s*.*?$',
            f'> **来源**: {links}',
            text,
            count=1,
            flags=re.MULTILINE,
        )
        if n:
            path.write_text(new_text, encoding="utf-8")
            print(f"updated: {rel}")
        else:
            print(f"no source line: {rel}")


if __name__ == '__main__':
    main()
