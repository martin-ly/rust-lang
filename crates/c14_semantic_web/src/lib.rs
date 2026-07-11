//! # Rust 知识体系语义 Web 工具链
//!
//! 本 crate 为 `concept/00_meta/kg_data_v3.json` 提供轻量级解析、验证、推理与查询能力。
//! 它是 Sophia / Oxigraph / rudof 等全功能 RDF 工具链的过渡与补充：
//!
//! - 不引入重型依赖，直接消费项目自定义的 JSON-LD v2/v3 格式。
//! - 提供图遍历、传递闭包、循环依赖检测等核心知识工程操作。
//! - 提供可扩展的验证框架，后续可替换为 SHACL 引擎。
//!
//! ## 快速开始
//!
//! ```no_run
//! use c14_semantic_web::io::load_kg_from_json;
//! use c14_semantic_web::validation::Validator;
//!
//! let kg = load_kg_from_json("concept/00_meta/kg_data_v3.json").unwrap();
//! let report = Validator::new().validate(&kg);
//! assert!(report.is_valid());
//! ```

pub mod graph;
pub mod io;
pub mod reasoning;
pub mod validation;

pub use graph::{Entity, EntityType, KnowledgeGraph, Relation, RelationMeta};
pub use validation::{ValidationReport, Validator};
