//! AFIDT (async fn in dyn trait) 跟踪模块（Nightly）
//! AFIDT (async fn in dyn trait) Tracking Module (Nightly)
//! 预计稳定版本: **1.97-1.98**。
//! this : **1.97-1.98**。
//!
//! # 概念定义
//! # Concept Definitions
//!
//! AFIDT 允许在 trait object (`dyn Trait`) 中使用 `async fn`。
//! async Rust finally main ， `async_trait` part scenario 。
//!
//! # 问题背景
//! # problem background
//!
//! ```text
//! AFIT (1.75.0): async fn in trait ✅
//!   └── 但 trait object (dyn Trait) 不支持 async fn ❌
//!           └── AFIDT (1.97+ nightly): 原生支持 dyn async trait ✅
//!
//! # 权威来源
//! # Authoritative Sources
//! - 跟踪: [rust-lang/rust#133119](https://github.com/rust-lang/rust/issues/133119)

// 注意：async_fn_in_dyn_trait feature 已在 lib.rs 中声明
// #![feature(async_fn_in_dyn_trait)]

#![allow(unexpected_cfgs)]
#![allow(async_fn_in_trait)]

// use std::future::Future; // 当前模块未直接使用

// ============================================================================
// 1. AFIDT 基础示例
// ============================================================================

/// # 原生 AFIDT vs async_trait 宏
/// ```ignore
/// use async_trait::async_trait;
///
/// #[async_trait]
/// trait DataSource {
///     async fn fetch(&self, key: &str) -> Option<String>;
/// }
/// ```
///
/// ## AFIDT 方式（nightly，未来 stable）
/// trait DataSource {
///     async fn fetch(&self, key: &str) -> Option<String>;
/// }
///
/// // ✅ AFIDT 的关键价值：dyn Trait 现在支持 async fn
/// fn create_source() -> Box<dyn DataSource> {
///     Box::new(Database)
/// }
/// ```
pub struct AfidtExamples;

/// 数据源 trait —— 使用原生 async fn
/// trait —— async fn
pub trait DataSource {
    async fn fetch(&self, key: &str) -> Option<String>;
    async fn exists(&self, key: &str) -> bool;
}

/// 数据库实现
/// datalibrary implementation
pub struct Database;

impl DataSource for Database {
    async fn fetch(&self, key: &str) -> Option<String> {
        Some(format!("db_value_for_{}", key))
    }

    async fn exists(&self, key: &str) -> bool {
        !key.is_empty()
    }
}

/// 缓存实现
pub struct Cache;

impl DataSource for Cache {
    async fn fetch(&self, key: &str) -> Option<String> {
        Some(format!("cached_value_for_{}", key))
    }

    async fn exists(&self, key: &str) -> bool {
        key.len() > 2
    }
}

/// 运行时分发枚举（AFIDT 当前限制：async trait 尚不支持 dyn）
/// Run enumAFIDT currentasync trait support dyn
pub enum DataSourceKind {
    Database(Database),
    Cache(Cache),
}

impl DataSource for DataSourceKind {
    async fn fetch(&self, key: &str) -> Option<String> {
        match self {
            DataSourceKind::Database(db) => db.fetch(key).await,
            DataSourceKind::Cache(c) => c.fetch(key).await,
        }
    }

    async fn exists(&self, key: &str) -> bool {
        match self {
            DataSourceKind::Database(db) => db.exists(key).await,
            DataSourceKind::Cache(c) => c.exists(key).await,
        }
    }
}

impl AfidtExamples {
    /// 使用枚举进行运行时分发（AFIDT 尚不完全支持 dyn Trait）
    /// enum runtime （AFIDT dyn Trait）
    pub fn create_source(kind: &str) -> DataSourceKind {
        match kind {
            "db" => DataSourceKind::Database(Database),
            _ => DataSourceKind::Cache(Cache),
        }
    }

    /// 泛型函数：接受任何 DataSource
    /// generic function ： DataSource
    pub async fn get_user_name<S: DataSource>(source: &S, user_id: u64) -> Option<String> {
        source.fetch(&format!("user:{}", user_id)).await
    }
}

// ============================================================================
// 2. 与 async_trait 的对比
// ============================================================================

/// # async_trait vs 原生 AFIDT
/// |------|---------------|---------------------|
/// | 额外依赖 | 需要 `async-trait` crate | 零依赖 |
/// | outside | `async-trait` crate | |
/// | 性能 | 额外 Box 分配（dyn Future） | 更优（无强制 Box） |
/// | performance | outside Box （dyn Future） | （ Box） |
/// | Send bound | 自动添加，可能过度约束 | 精确控制（需 RTN） |
/// | Send bound | ，may | （ RTN） |
/// | 编译错误 | 宏展开后信息模糊 | 原生错误信息 |
/// | | after vague | error message |
/// | 动态分发 | 支持 | ✅ 原生支持 |
/// | | | ✅ |
/// | 稳定状态 | ✅ Stable | Nightly |
pub struct AsyncTraitComparison;

impl AsyncTraitComparison {
    /// async_trait 的内部开销说明
    /// async_trait inside overhead explain
    pub fn async_trait_overhead() -> &'static str {
        "async_trait 宏将 async fn 转换为返回 Box<dyn Future + Send> 的普通 fn。这引入了堆分配和 \
         Send 约束，在某些场景下是过度约束。AFIDT 消除了这些开销。"
    }

    /// 迁移路径说明
    /// explain
    pub fn migration_path() -> &'static str {
        "1. 等待 AFIDT 稳定 (1.97-1.98)2. 移除 #[async_trait] 属性3. 移除 async-trait 依赖4. 检查 \
         Send bound 假设（可能需要 RTN）"
    }
}

// ============================================================================
// 3. 限制与反例
// ============================================================================

/// # AFIDT 当前限制
/// # AFIDT when before
///
/// ## ❌ Send bound 问题
/// AFIDT Future Send in trait bound in express 。
/// 需要 RTN (Return Type Notation) 解决。
/// ```text
/// // 当前无法表达：返回的 Future 必须是 Send 的
/// // when before express ： Future must Send
/// fn spawn_task<T>(source: T)
/// where
///     T: DataSource,  // DataSource::fetch 返回的 Future 是 Send 吗？
///     T: Send + 'static,
/// {
///     tokio::spawn(async move { source.fetch("key").await });
/// }
/// ```
///
/// ## ❌ 关联类型投影
/// ## ❌ associated type
/// 某些复杂的关联类型场景在 AFIDT 中仍有边界情况。
/// complex associated type scenario in AFIDT in edge situation 。
pub struct AfidtLimitations;

impl AfidtLimitations {
    /// 解释 Send bound 问题
    pub fn explain_send_bound_problem() -> &'static str {
        "AFIDT 的返回类型是 opaque impl Future，调用者无法知道它是否实现了 Send。这导致在 \
         tokio::spawn 等需要 Send Future 的场景中无法直接使用 dyn Trait。RTN (Return Type \
         Notation) 将提供 `Trait<method(): Send>` 语法来解决此问题。"
    }
}

// ============================================================================
// 4. RTN (Return Type Notation) 预研
// ============================================================================

/// # Return Type Notation (RTN)
///
/// RTN 解决 AFIDT 的 Send bound 问题，允许在 trait bound 中标注返回类型属性。
/// RTN AFIDT Send bound problem ，in trait bound in type attribute 。
///
/// ## 预研语法
/// ##
/// ```ignore
/// #![feature(return_type_notation)]
///
/// fn spawn_task<T>(source: T)
/// where
///     T: DataSource<fetch(): Send>,  // RTN：声明 fetch 返回 Send
///     T: Send + 'static,
/// {
///     tokio::spawn(async move { source.fetch("key").await });
/// }
/// ```
///
/// # 权威来源
/// # Authoritative Sources
/// - RFC: [RFC 3654](https://rust-lang.github.io/rfcs/3654-return-type-notation.html)
/// - 预计稳定: 1.97+
/// - : 1.97+
pub struct RtnPreview;

impl RtnPreview {
    /// RTN 语法预览
    /// RTN
    pub fn syntax_preview() -> &'static str {
        "T: DataSource<fetch(): Send>  // RTN 标注 fetch 返回 Send Future"
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_async_trait_overhead() {
        assert!(!AsyncTraitComparison::async_trait_overhead().is_empty());
    }

    #[test]
    fn test_migration_path() {
        assert!(!AsyncTraitComparison::migration_path().is_empty());
    }

    #[test]
    fn test_send_bound_explanation() {
        assert!(!AfidtLimitations::explain_send_bound_problem().is_empty());
    }

    #[test]
    fn test_rtn_syntax_preview() {
        assert_eq!(
            RtnPreview::syntax_preview(),
            "T: DataSource<fetch(): Send>  // RTN 标注 fetch 返回 Send Future"
        );
    }
}
