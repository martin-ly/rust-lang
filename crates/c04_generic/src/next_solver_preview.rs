//! Next-generation Trait Solver 预览
//!
//! 本模块演示 Rust 2026 旗舰稳定化目标 —— Next-generation trait solver 的
//! 核心改进与 nightly 代码体验。
//!
//! **编译要求**: 需要 nightly Rust + `RUSTFLAGS="-Znext-solver=globally"`
//! ```bash
//! RUSTFLAGS="-Znext-solver=globally" cargo +nightly check -p c04_generic
//! ```
//!
//! **来源**: [Rust Project Goals 2026 — Next-generation trait solver]
//! (https://rust-lang.github.io/rust-project-goals/2026/flagships.html)
//! · [rustc-next-trait-solver 源码]
//! (https://github.com/rust-lang/rust/tree/master/compiler/rustc_next_trait_solver)
//! · [来源: Rust Official Docs]

// ============================================================================
// 1. Coherence 改进：Previously-rejected 的合法代码
// ============================================================================

/// # 概念：新 Solver 对 Coherence 的放宽
///
/// 旧 solver 在某些 where-clause 场景下会**错误拒绝**合法的 impl，
/// 因为 coherence 检查无法从现有约束推导必然性。
/// 新 solver 使用更精确的逻辑推导，可正确接受这些代码。
///
/// **Bloom 层级**: 分析
///
/// ```rust,ignore
/// #![allow(incomplete_features)]
/// #![feature(next_solver)]
///
/// // 旧 solver 会错误拒绝此代码：
/// // "conflicting implementations"
/// // 新 solver 正确接受：where-clause 确保了互斥性
///
/// trait Process<T> {
///     fn process(&self, item: T);
/// }
///
/// struct Wrapper<T>(T);
///
/// // impl A: 仅当 T: Clone 时实现
/// impl<T: Clone> Process<T> for Wrapper<T> {
///     fn process(&self, item: T) {
///         let _ = item.clone();
///     }
/// }
///
/// // impl B: 仅当 T: Default 时实现
/// // 旧 solver 认为可能与 impl A 冲突（因为某类型可能同时实现 Clone + Default）
/// // 新 solver 理解：这在 coherence 层面是允许的（negative reasoning）
/// impl<T: Default> Process<T> for Wrapper<T> {
///     fn process(&self, item: T) {
///         let _ = T::default();
///     }
/// }
/// ```

// ============================================================================
// 2. Implied Bounds 自动推导
// ============================================================================

/// # 概念：减少手动 bound 标注
///
/// 新 solver 改进了 implied bounds 推导：
/// 从关联类型约束可自动推导出的 bound 不再需要显式写出。
///
/// **Bloom 层级**: 应用
///
/// ```rust,ignore
/// #![allow(incomplete_features)]
/// #![feature(next_solver)]
///
/// trait Container {
///     type Item;
/// }
///
/// // 旧 solver：需要显式写出 T: Container<Item = U>, U: Clone
/// // 新 solver：从 `T: Container<Item = U>` 可自动推导 `U` 需满足 `Clone`
/// fn duplicate_item<T, U>(container: &T) -> (U, U)
/// where
///     T: Container<Item = U>,
///     // 旧 solver 要求此显式标注：U: Clone,
/// {
///     // 如果 Container<Item = U> 的契约隐含 U: Clone，
///     // 新 solver 可自动推导
///     unimplemented!()
/// }
/// ```

// ============================================================================
// 3. GATs 与复杂生命周期约束
// ============================================================================

/// # 概念：GATs 的生命周期推导增强
///
/// 新 solver 显著改善了 GATs（Generic Associated Types）在
/// 复杂生命周期和 where-clause 场景下的推导能力。
///
/// **Bloom 层级**: 分析
///
/// ```rust,ignore
/// #![allow(incomplete_features)]
/// #![feature(generic_associated_types)]
/// #![feature(next_solver)]
///
/// // Lending Iterator —— 返回与 self 生命周期绑定的引用
/// trait LendingIterator {
///     type Item<'a>
///     where
///         Self: 'a;
///
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
///     // 旧 solver 常在此处失败：无法推导 Item<'b> = &'b [T] 满足 where Self: 'b
///     // 新 solver 正确理解：当 WindowIter<'a, T>: 'b 时，'a: 'b 即满足
///     type Item<'b> = &'b [T]
///     where
///         Self: 'b;
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

/// # 概念：Negative impls 的正确语义
///
/// `impl !Trait for T` 在新 solver 下获得与 coherence 的正确交互：
/// 编译器可安全地假设 `T` 绝不实现 `Trait`。
///
/// **Bloom 层级**: 评价
///
/// ```rust,ignore
/// #![feature(negative_impls)]
/// #![feature(next_solver)]
///
/// trait NotNull {}
///
/// // 明确声明：裸指针永不实现 NotNull
/// impl<T> !NotNull for *const T {}
/// impl<T> !NotNull for *mut T {}
///
/// // 因此，&T 自动满足 NotNull 的"排他"语义
/// struct SafeRef<T>(T);
/// impl<T> NotNull for SafeRef<T> {}
///
/// // 新 solver 保证：任何 *const T / *mut T 都无法通过 orphan rule
/// // 或其他方式获得 NotNull，因为 negative impl 是"最终"的
/// fn require_not_null<T: NotNull>(_: T) {}
/// ```

// ============================================================================
// 5. 编译器测试与迁移指南
// ============================================================================

/// # 测试 Next Solver 兼容性
///
/// ```bash
/// # 1. 全局启用（编译整个 crate）
/// RUSTFLAGS="-Znext-solver=globally" cargo +nightly check
///
/// # 2. 仅测试 coherence（不强制使用新 solver 求解所有 trait bound）
/// RUSTFLAGS="-Znext-solver=coherence" cargo +nightly check
///
/// # 3. 在 .cargo/config.toml 中配置（团队迁移）
/// # [build]
/// # rustflags = ["-Znext-solver=globally"]
/// # rustdocflags = ["-Znext-solver=globally"]
/// ```
///
/// **迁移检查清单**:
///
/// | 检查项 | 旧行为 | 新行为 | 你的代码是否受影响 |
/// |:---|:---|:---|:---:|
/// | Coherence 冲突 | 某些合法代码被拒绝 | 正确接受 | 🟡 检查编译错误 |
/// | 隐式 bound | 需显式标注 | 自动推导 | 🟢 通常受益 |
/// | 负向推导 | 受限 | 完整 | 🟢 可简化逻辑 |
/// | 编译时间 | 指数退化可能 | 线性改善 | 🟢 通常改善 |

// ============================================================================
// 6. 稳定化时间线跟踪
// ============================================================================

/// **稳定化预测**（基于 2026-05-21 公开信息）:
///
/// | 里程碑 | 预计时间 | 状态 |
/// |:---|:---:|:---|
/// | Coherence 迁移 | 2026 Q2 | 🟡 推进中 |
/// | 全局默认启用 | 2026 Q4–2027 Q1 | 🔴 计划 |
/// | 稳定版默认 | 2027 | 🔴 远期 |
///
/// **跟踪 Issue**:
/// - rust#107374: Next-gen trait solver 跟踪
/// - rust#105782: Coherence unsoundness（旧 solver）
/// - rust#109815: GATs 生命周期推导问题

// ============================================================================
// 模块导出（稳定 Rust 兼容的占位接口）
// ============================================================================

#[cfg(doc)]
mod doc_examples {
    //! 文档示例占位 —— 实际编译需要 nightly + `-Znext-solver`
}

/// 标记本模块需要 nightly 编译器
#[cfg(not(doc))]
pub const REQUIRES_NIGHTLY: bool = true;

/// 标记本模块需要的 solver 版本
#[cfg(not(doc))]
pub const SOLVER_VERSION: &str = "next-solver (globally)";
