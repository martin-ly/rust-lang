//! Next-generation Trait Solver 预览
//! **编译要求**: 需要 nightly Rust + `RUSTFLAGS="-Znext-solver=globally"`
//! **编译要求**: Requires nightly Rust + `RUSTFLAGS="-Znext-solver=globally"`
//! ```text
//! // 需要 nightly Rust + RUSTFLAGS="-Znext-solver=globally"
//! ```
//!
//! **来源**: [Rust Project Goals 2026 — Next-generation trait solver](https://rust-lang.github.io/rust-project-goals/2026/flagships.html)
//! **Source**: [Rust Project Goals 2026 — Next-generation trait solver](https://rust-lang.github.io/rust-project-goals/2026/flagships.html)
//! · [rustc-next-trait-solver 源码](https://github.com/rust-lang/rust/tree/master/compiler/rustc_next_trait_solver)
//! · [rustc-next-trait-solver source](https://github.com/rust-lang/rust/tree/master/compiler/rustc_next_trait_solver)
//! · [来源: Rust Official Docs]

// ============================================================================
// 1. Coherence 改进：Previously-rejected 的合法代码
// ============================================================================

/// # concept：新 Solver to Coherence 放宽
/// **Bloom 层级**: 分析
/// **Bloom **: analyze
/// **Bloom 层级**: analysis
/// ```text
/// #![allow(incomplete_features)]
/// #![feature(next_solver)]
///
/// // 旧 solver 会错误拒绝此代码：
/// trait SomeTrait<T> { fn process(&self, item: T); }
/// struct Wrapper<T>(T);
/// // impl A: 仅当 T: Clone 时实现
/// impl<T: Clone> SomeTrait<T> for Wrapper<T> { fn process(&self, item: T) { let _ = item.clone(); } }
/// // impl B: 仅当 T: Default 时实现
/// impl<T: Default> SomeTrait<T> for Wrapper<T> { fn process(&self, item: T) { let _ = T::default(); } }
/// ```

// ============================================================================
// 2. Implied Bounds 自动推导
// ============================================================================

/// # 概念：减少手动 bound 标注
/// # concept ： bound
/// # concept：减少手动 bound 标注
/// # concept： bound
/// **Bloom 层级**: 应用
/// **Bloom **: application
/// **Bloom 层级**: application
/// ```text
/// #![allow(incomplete_features)]
/// #![feature(next_solver)]
///
/// trait Container { type Item; }
/// // 旧 solver：需要显式写出 T: Container<Item = U>, U: Clone
/// // 新 solver：从 `T: Container<Item = U>` 可自动推导 `U` 需满足 `Clone`
/// fn process<T, U>(c: T)
/// where
///     T: Container<Item = U>,
///     // 旧 solver 要求此显式标注：U: Clone,
///     // 新 solver 可自动推导
/// {}
/// ```

// ============================================================================
// 3. GATs 与复杂生命周期约束
// ============================================================================

/// **Bloom 层级**: 分析
/// **Bloom **: analyze
/// **Bloom 层级**: analysis
/// ```text
/// #![allow(incomplete_features)]
/// #![feature(generic_associated_types)]
/// #![feature(next_solver)]
///
/// trait LendingIterator {
///     type Item<'a> where Self: 'a;
///     fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
/// }
///
/// struct WindowIter<'a, T> {
///     slice: &'a [T],
///     window_size: usize,
///     pos: usize,
/// }
///
/// impl<'a, T> LendingIterator for WindowIter<'a, T> {
///     // 旧 solver 常在此处失败
///     type Item<'b> = &'b [T] where Self: 'b;
///
///     fn next<'b>(&'b mut self) -> Option<Self::Item<'b>> {
///         let window = self.slice.get(self.pos..self.pos + self.window_size)?;
///         self.pos += 1;
///         Some(window)
///     }
/// }
/// ```

// ============================================================================
// 4. Negative Impls 与 Coherence
// ============================================================================

/// # concept：Negative impls 正确语义
/// 编译器可安全地假设 `T` 绝不实现 `Trait`。
/// hypothesize `T` `Trait`。
/// 编译器可安全地hypothesize `T` 绝不Implementation of `Trait`。
/// **Bloom 层级**: 评价
/// **Bloom **:
/// #![feature(negative_impls)]
/// #![feature(next_solver)]
///
/// trait NotNull {}
///
///
///
/// // 新 solver 保证：任何 *const T / *mut T 都无法通过 orphan rule
/// // 新 solver Guarantee：任何 *const T / *mut T 都无法Via orphan rule

// ============================================================================
// 5. 编译器测试与迁移指南
// ============================================================================

/// # 测试 Next Solver 兼容性
/// # Next Solver
/// # Test for Next Solver 兼容性
/// # 1. 全局启用（编译整个 crate）
/// # 1. global （ crate）
/// # 2. 仅测试 coherence（不强制使用新 solver 求解所有 trait bound）
/// # 2. coherence（ solver all trait bound）
/// # 2. 仅Test for coherence（不强制Use新 solver 求解所有 trait bound）
/// # 3. 在 .cargo/config.toml 中配置（团队迁移）
/// # 3. in.cargo/config.toml in （）
/// # rustdocflags = ["-Znext-solver=globally"]
/// ```text
/// 
/// **迁移检查清单**:
/// ****:
/// | 检查项 | 旧行为 | 新行为 | 你的代码是否受影响 |
/// | | as | as | impact |
/// | Coherence 冲突 | 某些合法代码被拒绝 | 正确接受 | 🟡 检查编译错误 |
/// | Coherence conflict | Some valid code is rejected | Correctly accepted | 🟡 Check compile errors |
/// | Coherence | is | | 🟡 |
/// | 隐式 bound | 需显式标注 | 自动推导 | 🟢 通常受益 |
/// | bound | | | 🟢 |
/// | 负向推导 | 受限 | 完整 | 🟢 可简化逻辑 |
/// | | | complete | 🟢 |
/// | 编译时间 | 指数退化可能 | 线性改善 | 🟢 通常改善 |
/// | compile-time | index may | line | 🟢 |

// ============================================================================
// 6. 稳定化时间线跟踪
// ============================================================================

/// **稳定化预测**（基于 2026-05-21 公开信息）:
/// **forecast **（ 2026-05-21 ）:
/// **稳定化forecast**（Based on 2026-05-21 公开信息）:
/// | 里程碑 | 预计时间 | 状态 |
/// | | time | state |
/// | 里程碑 | 预计time | state |
/// | | time | state |
/// | Coherence 迁移 | 2026 Q2 | 🟡 推进中 |
/// | Coherence migration | 2026 Q2 | 🟡 In progress |
/// | Coherence | 2026 Q2 | 🟡 in |
/// | Coherence 迁移 | 2026 Q2 | 🟡 推进in |
/// | 全局默认启用 | 2026 Q4–2027 Q1 | 🔴 计划 |
/// | Global default enable | 2026 Q4–2027 Q1 | 🔴 Planned |
/// | global | 2026 Q4–2027 Q1 | 🔴 plan |
/// | 稳定版默认 | 2027 | 🔴 远期 |
/// | Stable default | 2027 | 🔴 Long-term |
/// | | 2027 | 🔴 far-term |
/// | 稳定版默认 | 2027 | 🔴 far-term |
/// | | 2027 | 🔴 far-term |
/// **跟踪 Issue**:
/// **trace Issue**:
/// - rust#107374: Next-gen trait solver 跟踪
/// - rust#107374: Next-gen trait solver trace
/// - rust#105782: Coherence unsoundness（旧 solver）
/// - rust#109815: GATs 生命周期推导问题
/// - rust#109815: GATs lifetime problem

// ============================================================================
// 模块导出（稳定 Rust 兼容的占位接口）
// ============================================================================

#[cfg(doc)]
mod doc_examples {
    //! 文档示例占位 —— 实际编译需要 nightly + `-Znext-solver`
    //! example —— actual nightly + `-Znext-solver`
}

/// 标记本模块需要 nightly 编译器
/// mark this module nightly
#[cfg(not(doc))]
pub const REQUIRES_NIGHTLY: bool = true;

#[cfg(not(doc))]
pub const SOLVER_VERSION: &str = "next-solver (globally)";
