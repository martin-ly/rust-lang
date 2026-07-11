use indexmap::IndexMap;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet, VecDeque};

/// 知识图谱中的实体类型，对应本体的六类节点（v3 实际使用 Concept/Theory/Model/Primitive）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "PascalCase")]
pub enum EntityType {
    Concept,
    Theory,
    Model,
    Property,
    Rule,
    Primitive,
}

impl<'de> Deserialize<'de> for EntityType {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        let stripped = s.strip_prefix("ex:").unwrap_or(&s);
        match stripped {
            "Concept" => Ok(EntityType::Concept),
            "Theory" => Ok(EntityType::Theory),
            "Model" => Ok(EntityType::Model),
            "Property" => Ok(EntityType::Property),
            "Rule" => Ok(EntityType::Rule),
            "Primitive" => Ok(EntityType::Primitive),
            other => Err(serde::de::Error::custom(format!(
                "unknown entity type: {}",
                other
            ))),
        }
    }
}

impl EntityType {
    pub fn as_str(&self) -> &'static str {
        match self {
            EntityType::Concept => "Concept",
            EntityType::Theory => "Theory",
            EntityType::Model => "Model",
            EntityType::Property => "Property",
            EntityType::Rule => "Rule",
            EntityType::Primitive => "Primitive",
        }
    }
}

/// SKOS 风格的多语言标签。
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct LangString {
    #[serde(rename = "@value")]
    pub value: String,
    #[serde(rename = "@language")]
    pub language: String,
}

/// 知识图谱实体。
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Entity {
    #[serde(rename = "@id")]
    pub id: String,
    #[serde(rename = "@type")]
    pub ty: EntityType,
    #[serde(rename = "skos:prefLabel", default)]
    pub pref_label: Vec<LangString>,
    #[serde(rename = "skos:altLabel", default)]
    pub alt_label: Vec<LangString>,
    #[serde(rename = "skos:definition", default)]
    pub definition: Vec<LangString>,
    /// v3 实体使用 `skos:scopeNote` 作为英文摘要（v2 使用 `skos:definition`）。
    #[serde(rename = "skos:scopeNote", default)]
    pub scope_note: Vec<LangString>,
    /// v3 实体指向 concept/ 下的相对路径。
    #[serde(rename = "ex:path", default)]
    pub path: Option<String>,
    #[serde(rename = "ex:layer", default)]
    pub layer: Option<String>,
    #[serde(rename = "ex:bloom", default)]
    pub bloom: Option<String>,
    #[serde(rename = "ex:asp", default)]
    pub asp: Option<String>,
}

impl Entity {
    /// 获取指定语言的首选标签。
    ///
    /// v3 中部分实体的 `zh` 标签为空字符串；此时回退到 `en` 标签。
    pub fn label_for(&self, lang: &str) -> Option<&str> {
        for wanted in [lang, "en"] {
            if let Some(label) = self
                .pref_label
                .iter()
                .find(|l| l.language == wanted && !l.value.is_empty())
            {
                return Some(label.value.as_str());
            }
        }
        None
    }

    /// 获取实体的英文摘要（优先 `skos:definition`，v3 回退到 `skos:scopeNote`）。
    pub fn summary_for(&self, lang: &str) -> Option<&str> {
        self.definition
            .iter()
            .chain(self.scope_note.iter())
            .find(|l| l.language == lang)
            .map(|l| l.value.as_str())
    }

    /// 获取实体的短 ID（去掉命名空间前缀）。
    pub fn short_id(&self) -> &str {
        self.id.strip_prefix("ex:").unwrap_or(&self.id)
    }
}

/// 关系三元组上的元数据（RDF-star 注解）。
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RelationMeta {
    #[serde(rename = "ex:source")]
    pub source: String,
    #[serde(rename = "ex:confidence")]
    pub confidence: Option<f32>,
    #[serde(rename = "ex:version")]
    pub version: Option<String>,
    #[serde(rename = "ex:reviewed")]
    pub reviewed: Option<bool>,
}

/// 知识图谱关系。
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Relation {
    pub subject: String,
    pub predicate: String,
    pub object: String,
    #[serde(flatten)]
    pub meta: RelationMeta,
}

/// 知识图谱。
#[derive(Debug, Clone, Default)]
pub struct KnowledgeGraph {
    entities: IndexMap<String, Entity>,
    relations: Vec<Relation>,
    adjacency: HashMap<String, Vec<(String, String)>>, // subject -> [(predicate, object)]
}

impl KnowledgeGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_entity(&mut self, entity: Entity) {
        self.adjacency.entry(entity.id.clone()).or_default();
        self.entities.insert(entity.id.clone(), entity);
    }

    pub fn add_relation(&mut self, relation: Relation) {
        self.adjacency
            .entry(relation.subject.clone())
            .or_default()
            .push((relation.predicate.clone(), relation.object.clone()));
        self.relations.push(relation);
    }

    pub fn entities(&self) -> &IndexMap<String, Entity> {
        &self.entities
    }

    pub fn relations(&self) -> &[Relation] {
        &self.relations
    }

    pub fn get_entity(&self, id: &str) -> Option<&Entity> {
        self.entities.get(id)
    }

    pub fn get_relations_from(&self, subject: &str) -> Vec<&Relation> {
        self.relations
            .iter()
            .filter(|r| r.subject == subject)
            .collect()
    }

    pub fn get_relations_with_predicate(&self, predicate: &str) -> Vec<&Relation> {
        self.relations
            .iter()
            .filter(|r| r.predicate == predicate)
            .collect()
    }

    /// 查找从 `start` 出发、沿指定谓词可达的所有节点（BFS）。
    /// 返回集合不包含 `start` 自身。
    pub fn reachable(&self, start: &str, predicate: &str) -> HashSet<String> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        // 从 start 的直接后继开始遍历，不将 start 自身计入结果
        if let Some(edges) = self.adjacency.get(start) {
            for (pred, obj) in edges {
                if pred == predicate && !visited.contains(obj) {
                    visited.insert(obj.clone());
                    queue.push_back(obj.clone());
                }
            }
        }

        while let Some(current) = queue.pop_front() {
            if let Some(edges) = self.adjacency.get(&current) {
                for (pred, obj) in edges {
                    if pred == predicate && !visited.contains(obj) {
                        visited.insert(obj.clone());
                        queue.push_back(obj.clone());
                    }
                }
            }
        }
        visited
    }

    /// 计算指定谓词的传递闭包。
    pub fn transitive_closure(&self, predicate: &str) -> HashMap<String, HashSet<String>> {
        let mut closure: HashMap<String, HashSet<String>> = HashMap::new();
        for id in self.entities.keys() {
            closure.insert(id.clone(), self.reachable(id, predicate));
        }
        closure
    }

    /// 检测指定谓词是否存在循环依赖。
    pub fn detect_cycles(&self, predicate: &str) -> Vec<Vec<String>> {
        let mut cycles = Vec::new();
        let mut visited = HashSet::new();
        let mut stack = Vec::new();
        let mut on_stack = HashSet::new();

        for start in self.entities.keys() {
            if visited.contains(start) {
                continue;
            }
            self.dfs_cycles(
                start,
                predicate,
                &mut visited,
                &mut stack,
                &mut on_stack,
                &mut cycles,
            );
        }
        cycles
    }

    fn dfs_cycles(
        &self,
        node: &str,
        predicate: &str,
        visited: &mut HashSet<String>,
        stack: &mut Vec<String>,
        on_stack: &mut HashSet<String>,
        cycles: &mut Vec<Vec<String>>,
    ) {
        visited.insert(node.to_string());
        stack.push(node.to_string());
        on_stack.insert(node.to_string());

        if let Some(edges) = self.adjacency.get(node) {
            for (pred, obj) in edges {
                if pred != predicate {
                    continue;
                }
                if !visited.contains(obj) {
                    self.dfs_cycles(obj, predicate, visited, stack, on_stack, cycles);
                } else if on_stack.contains(obj) {
                    // 发现环
                    if let Some(pos) = stack.iter().position(|x| x == obj) {
                        let cycle = stack[pos..].to_vec();
                        cycles.push(cycle);
                    }
                }
            }
        }

        stack.pop();
        on_stack.remove(node);
    }
}
