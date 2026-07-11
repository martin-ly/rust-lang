use crate::graph::{Entity, KnowledgeGraph, Relation};
use serde_json::Value;
use std::collections::HashMap;
use std::fs;
use std::path::Path;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum KgIoError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("JSON parse error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("Missing field: {0}")]
    MissingField(String),
    #[error("Unexpected entity type: {0}")]
    UnexpectedType(String),
}

/// 从 JSON-LD v2/v3 文件加载知识图谱。
///
/// 当前实现解析项目自定义的 JSON-LD 简化格式，尚未使用完整 JSON-LD 处理算法。
/// v3 的 `entities` 为扁平数组；v2 为按类别分组的字典，两种布局均可解析。
/// 后续可替换为 sophia_jsonld 或 json-ld crate。
pub fn load_kg_from_json<P: AsRef<Path>>(path: P) -> Result<KnowledgeGraph, KgIoError> {
    let content = fs::read_to_string(path)?;
    let value: Value = serde_json::from_str(&content)?;

    let mut kg = KnowledgeGraph::new();

    // 加载类定义（可选，当前仅记录）
    if let Some(classes) = value.get("classes").and_then(|v| v.as_array()) {
        for _class in classes {
            // 类定义用于验证，当前版本不加入实体图
        }
    }

    // 加载实体：v3 为扁平数组，v2 为按类别分组的字典
    if let Some(entities) = value.get("entities") {
        if let Some(arr) = entities.as_array() {
            for item in arr {
                let entity: Entity = serde_json::from_value(item.clone())?;
                kg.add_entity(entity);
            }
        } else if let Some(groups) = entities.as_object() {
            for (_category, items) in groups {
                if let Some(arr) = items.as_array() {
                    for item in arr {
                        let entity: Entity = serde_json::from_value(item.clone())?;
                        kg.add_entity(entity);
                    }
                }
            }
        }
    }

    // 加载关系（RDF-star 注解格式）
    if let Some(relations) = value.get("relations").and_then(|v| v.as_array()) {
        for rel in relations {
            let relation = Relation {
                subject: rel
                    .get("ex:subject")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| KgIoError::MissingField("ex:subject".into()))?
                    .to_string(),
                predicate: rel
                    .get("ex:predicate")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| KgIoError::MissingField("ex:predicate".into()))?
                    .to_string(),
                object: rel
                    .get("ex:object")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| KgIoError::MissingField("ex:object".into()))?
                    .to_string(),
                meta: serde_json::from_value(rel.clone())?,
            };
            kg.add_relation(relation);
        }
    }

    Ok(kg)
}

/// 将知识图谱导出为简化的邻接表 JSON，便于前端可视化。
pub fn export_adjacency_json(kg: &KnowledgeGraph) -> Result<String, KgIoError> {
    let mut adjacency: HashMap<String, Vec<HashMap<String, String>>> = HashMap::new();
    for relation in kg.relations() {
        let entry = adjacency.entry(relation.subject.clone()).or_default();
        let mut map = HashMap::new();
        map.insert("predicate".into(), relation.predicate.clone());
        map.insert("object".into(), relation.object.clone());
        map.insert("source".into(), relation.meta.source.clone());
        if let Some(c) = relation.meta.confidence {
            map.insert("confidence".into(), c.to_string());
        }
        entry.push(map);
    }
    Ok(serde_json::to_string_pretty(&adjacency)?)
}
