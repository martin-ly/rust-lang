//! Cargo SemVer Checks 专题指南
//!
//! **版本 attribution**: Rust 1.95+ 生态实践
//!
//! 本模块系统介绍 Rust 语义化版本控制（Semantic Versioning）的核心概念、
//! Cargo 的 SemVer 规则、`cargo-semver-checks` 工具的使用方法，
//! 以及如何在日常开发中避免无意的 API 破坏性变更。
//!
//! ## 目录
//!
//! 1. [什么是 Semantic Versioning](#什么是-semantic-versioning)
//! 2. [为什么 API Breakage 很重要](#为什么-api-breakage-很重要)
//! 3. [cargo-semver-checks 工具](#cargo-semver-checks-工具)
//! 4. [常见 Breaking Changes](#常见-breaking-changes)
//! 5. [Deprecated 与迁移路径](#deprecated-与迁移路径)
//! 6. [CI/CD 集成](#cicd-集成)
//!
//! ## Mermaid: SemVer 决策流程
//!
//! ```mermaid
//! flowchart TD
//!     A[代码变更] --> B{是否修改 public API?}
//!     B -->|否| C[PATCH]
//!     B -->|是| D{是否向后兼容?}
//!     D -->|是| E[MINOR]
//!     D -->|否| F[MAJOR]
//!     F --> G[运行 cargo-semver-checks 验证]
//! ```

// ============================================================================
// 1. 什么是 Semantic Versioning
// ============================================================================

/// SemVer 版本号格式：`MAJOR.MINOR.PATCH`
///
/// - **MAJOR**: 破坏性变更（breaking changes），不向后兼容。
/// - **MINOR**: 向后兼容的功能新增。
/// - **PATCH**: 向后兼容的问题修复。
///
/// Rust 生态通过 Cargo 强制遵循 SemVer：一旦 crate 发布到 crates.io，
/// 下游用户依赖解析器会基于 SemVer 约束自动选择兼容版本。
pub struct SemVerBasics;

impl SemVerBasics {
    /// 示例版本号解析
    pub fn version_examples() {
        // 1.0.0 -> MAJOR=1, MINOR=0, PATCH=0
        // 1.2.3 -> MAJOR=1, MINOR=2, PATCH=3
        // 0.x.y -> 0.x 系列视为不稳定，允许 breaking changes
    }
}

// ============================================================================
// 2. 为什么 API Breakage 很重要
// ============================================================================

/// Cargo 的 SemVer 规则基于 Rust 类型系统和可见性。
///
/// 以下变更**通常**被视为 breaking：
/// - 删除 `pub` 函数、类型、模块、trait。
/// - 给非 `#[non_exhaustive]` 的 `pub struct` 添加字段。
/// - 收窄泛型约束（如从 `T` 改为 `T: Clone`）。
/// - 修改 trait 的 required method 签名（无默认实现时）。
/// - 改变 `pub` 常量的类型或值（若被用于模式匹配）。
///
/// 以下变更**通常**视为 compatible：
/// - 给 `#[non_exhaustive]` 的 enum 添加 variant。
/// - 给 trait 添加带有默认实现的方法。
/// - 放宽函数参数类型（需保持调用端兼容）。
pub struct ApiBreakageConcepts;

// ============================================================================
// 3. cargo-semver-checks 工具
// ============================================================================

/// `cargo-semver-checks` 是基于 rustdoc JSON 的静态分析工具，
/// 用于检测当前 crate 的公共 API 是否违反了 SemVer 规则。
///
/// ## 安装
///
/// ```bash
/// cargo install cargo-semver-checks --locked
/// ```
///
/// ## 基本用法
///
/// ```bash
/// # 检查当前 crate
/// cargo semver-checks
///
/// # 与已发布版本对比
/// cargo semver-checks --baseline-version 0.1.0
///
/// # 与 git 标签对比
/// cargo semver-checks --baseline-rev v0.1.0
/// ```
///
/// ## 检测范围
///
/// | 变更类型 | 检测能力 | 违反的 SemVer |
/// |---------|---------|-------------|
/// | 删除公共函数/类型 | ✅ | MAJOR |
/// | 给非 exhaustive struct 添加字段 | ✅ | MAJOR |
/// | 收窄函数返回类型 | ✅ | MAJOR |
/// | trait 新增 required method | ✅ | MAJOR |
/// | 给 enum 添加 variant（无 non_exhaustive） | ✅ | MAJOR |
/// | 修改文档 | ❌ | N/A |
/// | 行为变更 | ❌ | 需人工审查 |
pub struct CargoSemverChecksTool;

// ============================================================================
// 4. 常见 Breaking Changes 与防御模式
// ============================================================================

// ---------------------------------------------------------------------------
// 4.1 Enum variant 添加
// ---------------------------------------------------------------------------

/// **问题**: 给 `pub enum` 添加 variant 会破坏所有使用 exhaustive match 的下游代码。
///
/// **解决方案**: 使用 `#[non_exhaustive]` 属性。
///
/// ```rust
/// #[non_exhaustive]
/// pub enum NetworkEvent {
///     Connected,
///     Disconnected,
///     // 未来可安全添加：DataReceived,
/// }
/// ```
///
/// 下游必须写 `_ => {}` 分支，从而允许未来扩展。
#[non_exhaustive]
pub enum NetworkEvent {
    Connected,
    Disconnected,
}

// ---------------------------------------------------------------------------
// 4.2 Trait method 添加
// ---------------------------------------------------------------------------

/// **问题**: 给 `pub trait` 添加 required method 会破坏所有外部实现者。
///
/// **解决方案**: 提供默认实现，或使用 sealed trait 模式。
///
/// ```rust
/// pub trait ProtocolHandler {
///     fn handle(&self, data: &[u8]);
///     // 新增方法时提供默认实现
///     fn handle_async(&self, _data: &[u8]) -> std::future::Ready<()> {
///         std::future::ready(())
///     }
/// }
/// ```
pub trait ProtocolHandler {
    fn handle(&self, data: &[u8]);

    /// Rust 1.95+ 实践：新增方法必须附带默认实现，避免 breaking change。
    fn handle_async(&self, _data: &[u8]) -> std::future::Ready<()> {
        std::future::ready(())
    }
}

// ---------------------------------------------------------------------------
// 4.3 Type changes（类型变更）
// ---------------------------------------------------------------------------

/// **问题**: 直接修改 `pub type` 或结构体字段类型会导致下游编译失败。
///
/// **解决方案**:
/// - 使用 type alias 渐进迁移。
/// - 使用 newtype 模式封装。
/// - 保留旧类型并标记 `#[deprecated]`。

/// 旧类型（已废弃）
#[deprecated(since = "0.2.0", note = "请使用 `PacketId` 替代")]
pub type OldPacketId = u32;

/// 新类型：使用 newtype 模式增强类型安全
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PacketId(pub u64);

impl PacketId {
    /// 从旧类型迁移
    pub fn from_legacy(id: u32) -> Self {
        Self(id as u64)
    }
}

// ---------------------------------------------------------------------------
// 4.4 Sealed trait 模式
// ---------------------------------------------------------------------------

/// 若不希望外部 crate 实现某个 trait，可使用 sealed trait 防止未来扩展导致的 breakage。
mod sealed {
    pub trait Sealed {}
}

/// 公开 trait 但隐藏 sealed 父 trait，阻止外部实现。
pub trait InternalTrait: sealed::Sealed {
    fn do_something(&self);
}

impl sealed::Sealed for String {}
impl InternalTrait for String {
    fn do_something(&self) {}
}

// ============================================================================
// 5. Deprecated 与迁移路径
// ============================================================================

/// `#[deprecated]` 是 Rust 提供的标准属性，用于标记即将移除的 API，
/// 给下游开发者留出迁移时间。
///
/// ## 使用规范
///
/// - `since = "x.y.z"`: 标记从哪个版本开始废弃。
/// - `note = "..."`: 提供替代方案或迁移说明。
///
/// ## 示例：函数废弃
///
/// ```rust
/// #[deprecated(since = "0.3.0", note = "请使用 `connect_async` 替代")]
/// pub fn connect_legacy(addr: &str) -> std::io::Result<()> {
///     // ...
///     # Ok(())
/// }
/// ```
///
/// ## 迁移路径设计原则
///
/// 1. **MAJOR 版本前至少保留一个 MINOR 周期的 deprecated API**。
/// 2. **在文档中提供 before/after 代码对比**。
/// 3. **若涉及类型变更，提供 `From` / `Into` 转换**。

/// 已废弃的 legacy 连接函数
#[deprecated(since = "0.3.0", note = "请使用 `connect_async` 替代")]
pub fn connect_legacy(_addr: &str) -> std::io::Result<()> {
    Ok(())
}

/// 推荐的异步连接函数（占位）
pub async fn connect_async(_addr: &str) -> std::io::Result<()> {
    Ok(())
}

/// 为平滑迁移提供 `From` 实现
#[derive(Debug)]
pub struct LegacyConfig {
    pub timeout_ms: u32,
}

#[derive(Debug)]
pub struct NewConfig {
    pub timeout: std::time::Duration,
}

impl From<LegacyConfig> for NewConfig {
    fn from(cfg: LegacyConfig) -> Self {
        Self {
            timeout: std::time::Duration::from_millis(cfg.timeout_ms as u64),
        }
    }
}

// ============================================================================
// 6. CI/CD 集成
// ============================================================================

/// 在 CI 中集成 `cargo-semver-checks` 可防止无意的 breaking change 进入主分支。
///
/// ## GitHub Actions 示例
///
/// ```yaml
/// semver-checks:
///   name: SemVer Checks
///   runs-on: ubuntu-latest
///   steps:
///     - uses: actions/checkout@v4
///       with:
///         fetch-depth: 0
///
///     - uses: dtolnay/rust-toolchain@stable
///
///     - name: Install cargo-semver-checks
///       run: cargo install cargo-semver-checks --locked
///
///     - name: Run semver checks
///       run: cargo semver-checks --workspace
/// ```
///
/// ## CI 策略建议
///
/// 1. **PR 检查**: 与 `main` 分支对比，阻止无意的 breaking change。
/// 2. **发布前检查**: 与上一个发布的版本对比。
/// 3. **允许失败模式**: 对于实验性 crate，可设置 `continue-on-error: true`。

/// Mermaid: CI 流水线中的 SemVer 检查
///
/// ```mermaid
/// flowchart LR
///     A[Pull Request] --> B[Build & Test]
///     B --> C[cargo-semver-checks]
///     C -->|Pass| D[Merge]
///     C -->|Fail| E[Review Breaking Change]
///     E -->|Intentional| F[Update MAJOR Version]
///     E -->|Unintentional| G[Revert / Fix]
///     F --> D
///     G --> B
/// ```
pub struct CiCdIntegration;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_non_exhaustive_enum() {
        // 由于 NetworkEvent 标记了 #[non_exhaustive]，
        // 即使在同一 crate 内，match 也需要处理 _ => {}
        let evt = NetworkEvent::Connected;
        let _desc = match evt {
            NetworkEvent::Connected => "connected",
            NetworkEvent::Disconnected => "disconnected",
            // 必须保留通配分支以演示兼容性
            _ => "unknown",
        };
        assert!(!_desc.is_empty());
    }

    #[test]
    fn test_deprecated_migration() {
        let legacy = LegacyConfig { timeout_ms: 5000 };
        let new: NewConfig = legacy.into();
        assert_eq!(new.timeout, std::time::Duration::from_millis(5000));
    }

    #[test]
    fn test_packet_id_migration() {
        let pid = PacketId::from_legacy(42);
        assert_eq!(pid.0, 42);
    }
}
