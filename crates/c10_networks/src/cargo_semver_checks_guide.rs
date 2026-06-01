//! **版本 attribution**: Rust 1.95+ 生态实践
//! 以及如何在日常开发中避免无意的 API 破坏性变更。
//! and in in API 。
//! ## 目录
//! ##
//! 2. [as什么 API Breakage 很important](#as什么-api-breakage-很important)
//! 3. [cargo-semver-checks 工具](#cargo-semver-checks-工具)
//! 4. [常见 Breaking Changes](#常见-breaking-changes)
//! 6. [CI/CD 集成](#cicd-集成)
//! 6. [CI/CD ](#cicd-)
//! flowchart TD
//!     B -->|否| C[PATCH]
//!     B -->|是| D{是否向后兼容?}
//!     B -->|| D{after?}
//!     D -->|否| F[MAJOR]
//!     F --> G[运行 cargo-semver-checks 验证]

// ============================================================================
// 1. 什么是 Semantic Versioning
// ============================================================================

/// - **MAJOR**: 破坏性变更（breaking changes），不向后兼容。
/// - **MAJOR**: （breaking changes），after 。
pub struct SemVerBasics;

impl SemVerBasics {
    /// 示例版本号解析
    /// example this
    pub fn version_examples() {
        // 1.0.0 -> MAJOR=1, MINOR=0, PATCH=0
        // 1.2.3 -> MAJOR=1, MINOR=2, PATCH=3
        // 0.x.y -> 0.x 系列视为不稳定，允许 breaking changes
    }
}

// ============================================================================
// 2. 为什么 API Breakage 很重要
// ============================================================================

/// - 删除 `pub` 函数、类型、模块、trait。
/// - `pub` function 、type 、module 、trait。
/// - 给非 `#[non_exhaustive]` `pub struct` 添加field。
/// - 改变 `pub` 常量的类型或值（若被用于模式匹配）。
/// - `pub` constant type or （is ）。
/// - 给 `#[non_exhaustive]` enum 添加 variant。
/// - 给 trait 添加带有default implementationmethod。
/// - 放宽函数参数类型（需保持调用端兼容）。
/// - function parameter type （）。
pub struct ApiBreakageConcepts;

// ============================================================================
// 3. cargo-semver-checks 工具
// ============================================================================

/// ## 安装
/// ##
/// cargo install cargo-semver-checks --locked
/// ```
///
/// ## 基本用法
/// ## this usage
/// ## this
/// # 检查当前 crate
/// # when before crate
///
/// # 与已发布版本对比
/// # and this to
/// # 与 git 标签对比
/// # and git to
/// # and git 标签to比
///
/// ## 检测范围
/// ## scope
/// ## 检测range
/// | 删除公共函数/类型 | ✅ | MAJOR |
/// | function /type | ✅ | MAJOR |
/// | 给非 exhaustive struct 添加字段 | ✅ | MAJOR |
/// | 给非 exhaustive struct 添加field | ✅ | MAJOR |
/// | 收窄函数返回类型 | ✅ | MAJOR |
/// | function type | ✅ | MAJOR |
/// | trait 新增 required method | ✅ | MAJOR |
/// | 给 enum 添加 variant（无 non_exhaustive） | ✅ | MAJOR |
/// | 修改文档 | ❌ | N/A |
/// | | ❌ | N/A |
/// | 行为变更 | ❌ | 需人工审查 |
/// | as | ❌ | |
pub struct CargoSemverChecksTool;

// ============================================================================
// 4. 常见 Breaking Changes 与防御模式
// ============================================================================

// ---------------------------------------------------------------------------
// 4.1 Enum variant 添加
// ---------------------------------------------------------------------------

/// **解决方案**: 使用 `#[non_exhaustive]` 属性。
/// **solution **: `#[non_exhaustive]` attribute 。
/// ```rust
/// #[non_exhaustive]
/// pub enum NetworkEvent {
///     Connected,
///     Disconnected,
///
/// 下游必须写 `_ => {}` 分支，从而允许未来扩展。
/// under must `_ => {}` ，thereby allow future 。
/// under must `_ => {}` ，thereby future 。
#[non_exhaustive]
pub enum NetworkEvent {
    Connected,
    Disconnected,
}

// ---------------------------------------------------------------------------
// 4.2 Trait method 添加
// ---------------------------------------------------------------------------

/// **问题**: 给 `pub trait` 添加 required method 会破坏所有外部实现者。
/// **problem **: `pub trait` required method all outside 。
/// **解决方案**: 提供默认实现，或使用 sealed trait 模式。
/// **solution **: default implementation ，or sealed trait 。
/// pub trait ProtocolHandler {
///     fn handle(&self, data: &[u8]);
///     // 新增方法时提供默认实现
///     // method default implementation
///     }
/// ```
pub trait ProtocolHandler {
    fn handle(&self, data: &[u8]);

    /// Rust 1.95+ 实践：新增方法必须附带默认实现，避免 breaking change。
    /// Rust 1.95+ ：method must default implementation ， breaking change。
    fn handle_async(&self, _data: &[u8]) -> std::future::Ready<()> {
        std::future::ready(())
    }
}

// ---------------------------------------------------------------------------
// 4.3 Type changes（类型变更）
// ---------------------------------------------------------------------------

/// **问题**: 直接修改 `pub type` 或结构体字段类型会导致下游编译失败。
/// **problem **: `pub type` or struct field type under failure 。
/// **problem **: `pub type` or struct field type under 。
/// **解决方案**:
/// **solution **:
/// - 使用 type alias 渐进迁移。
/// - type alias 。
/// - Use type alias 渐进迁移。
/// - 使用 newtype 模式封装。
/// - newtype 。
/// - Use newtype 模式封装。
/// - 保留旧类型并标记 `#[deprecated]`。
/// - type and mark `#[deprecated]`。
/// - 保留旧typeandmark `#[deprecated]`。
/// 旧类型（已废弃）
/// type （）
#[deprecated(since = "0.2.0", note = "请使用 `PacketId` 替代")]
pub type OldPacketId = u32;

/// 新类型：使用 newtype 模式增强类型安全
/// type ： newtype type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PacketId(pub u64);

impl PacketId {
    /// 从旧类型迁移
    /// from type
    pub fn from_legacy(id: u32) -> Self {
        Self(id as u64)
    }
}

// ---------------------------------------------------------------------------
// 4.4 Sealed trait 模式
// ---------------------------------------------------------------------------

mod sealed {
    pub trait Sealed {}
}

/// 公开 trait 但隐藏 sealed 父 trait，阻止外部实现。
/// trait but hide sealed trait，outside 。
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

/// 给下游开发者留出迁移时间。
/// under time 。
/// ## 使用规范
/// ## norm
/// - `since = "x.y.z"`: 标记从哪个版本开始废弃。
/// - `since = "x.y.z"`: mark from this 。
/// - `note = "..."`: 提供替代方案或迁移说明。
/// - `note = "..."`: or explain 。
/// ## 示例：函数废弃
/// ## example ：function
/// #[deprecated(since = "0.3.0", note = "请使用 `connect_async` 替代")]
/// #[deprecated(since = "0.3.0", note = "请Use `connect_async` 替代")]
///     # Ok(())
/// }
/// ```
///
/// ## 迁移路径设计原则
/// ## design principle
/// ## 迁移路径designprinciple
/// 2. **在文档中提供 before/after 代码对比**。
/// 2. **in in before/after to **。
/// 3. **若涉及类型变更，提供 `From` / `Into` 转换**。
/// 3. **and type ， `From` / `Into` conversion **。
/// 已废弃 legacy Connectfunction
#[deprecated(since = "0.3.0", note = "请使用 `connect_async` 替代")]
pub fn connect_legacy(_addr: &str) -> std::io::Result<()> {
    Ok(())
}

/// 推荐的异步连接函数（占位）
/// async function （）
pub async fn connect_async(_addr: &str) -> std::io::Result<()> {
    Ok(())
}

/// as平滑迁移Provides `From` Implementation of
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
/// ## CI strategy
/// 1. **PR Check**: and `main` 分支to比，阻止无意 breaking change。
/// 2. **发布前检查**: 与上一个发布的版本对比。
/// 2. **before **: and on this to 。
/// 3. **允许失败模式**: 对于实验性 crate，可设置 `continue-on-error: true`。
/// 3. **allow failure **: to crate， `continue-on-error: true`。
/// 3. ****: to crate， `continue-on-error: true`。
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
