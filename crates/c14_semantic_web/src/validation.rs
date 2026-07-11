use crate::graph::{Entity, EntityType, KnowledgeGraph};

const VALID_LAYERS: &[&str] = &["L0", "L1", "L2", "L3", "L4", "L5", "L6", "L7"];
const VALID_BLOOM: &[&str] = &[
    "Remember",
    "Understand",
    "Apply",
    "Analyze",
    "Evaluate",
    "Create",
];
const VALID_RELATIONS: &[&str] = &[
    "ex:dependsOn",
    "ex:entails",
    "ex:mutexWith",
    "ex:refines",
    "ex:equivalentTo",
    "ex:counterExample",
    "ex:instanceOf",
    "ex:appliesTo",
    // v3 新增谓词（见 kg_data_v3.json properties 段）
    "ex:relatedTo",
];

/// 验证问题。
#[derive(Debug, Clone)]
pub struct ValidationIssue {
    pub severity: Severity,
    pub target: String,
    pub message: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Info,
}

/// 验证报告。
#[derive(Debug, Clone, Default)]
pub struct ValidationReport {
    pub issues: Vec<ValidationIssue>,
}

impl ValidationReport {
    pub fn is_valid(&self) -> bool {
        !self
            .issues
            .iter()
            .any(|i| matches!(i.severity, Severity::Error))
    }

    pub fn errors(&self) -> Vec<&ValidationIssue> {
        self.issues
            .iter()
            .filter(|i| matches!(i.severity, Severity::Error))
            .collect()
    }

    pub fn warnings(&self) -> Vec<&ValidationIssue> {
        self.issues
            .iter()
            .filter(|i| matches!(i.severity, Severity::Warning))
            .collect()
    }
}

/// 知识图谱验证器。
pub struct Validator {
    require_en_zh_pref_label: bool,
    require_relation_meta: bool,
}

impl Default for Validator {
    fn default() -> Self {
        Self {
            require_en_zh_pref_label: true,
            require_relation_meta: true,
        }
    }
}

impl Validator {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn validate(&self, kg: &KnowledgeGraph) -> ValidationReport {
        let mut report = ValidationReport::default();

        for entity in kg.entities().values() {
            self.validate_entity(entity, &mut report);
        }

        for relation in kg.relations() {
            self.validate_relation(relation, kg, &mut report);
        }

        report
    }

    fn validate_entity(&self, entity: &Entity, report: &mut ValidationReport) {
        // SKOS prefLabel 检查
        let has_en = entity.label_for("en").is_some();
        let has_zh = entity.label_for("zh").is_some();

        if self.require_en_zh_pref_label {
            if !has_en {
                report.issues.push(ValidationIssue {
                    severity: Severity::Error,
                    target: entity.id.clone(),
                    message: "缺少英文 skos:prefLabel (@language=en)".into(),
                });
            }
            if !has_zh {
                report.issues.push(ValidationIssue {
                    severity: Severity::Error,
                    target: entity.id.clone(),
                    message: "缺少中文 skos:prefLabel (@language=zh)".into(),
                });
            }
        }

        if entity.pref_label.is_empty() {
            report.issues.push(ValidationIssue {
                severity: Severity::Error,
                target: entity.id.clone(),
                message: "缺少 skos:prefLabel".into(),
            });
        }

        // Concept 专用检查
        if entity.ty == EntityType::Concept {
            if let Some(layer) = &entity.layer {
                if !VALID_LAYERS.contains(&layer.as_str()) {
                    report.issues.push(ValidationIssue {
                        severity: Severity::Error,
                        target: entity.id.clone(),
                        message: format!("无效的 ex:layer: {}", layer),
                    });
                }
            } else {
                report.issues.push(ValidationIssue {
                    severity: Severity::Warning,
                    target: entity.id.clone(),
                    message: "Concept 缺少 ex:layer".into(),
                });
            }

            if let Some(bloom) = &entity.bloom
                && !VALID_BLOOM.contains(&bloom.as_str())
            {
                report.issues.push(ValidationIssue {
                    severity: Severity::Error,
                    target: entity.id.clone(),
                    message: format!("无效的 ex:bloom: {}", bloom),
                });
            }
        }
    }

    fn validate_relation(
        &self,
        relation: &crate::graph::Relation,
        kg: &KnowledgeGraph,
        report: &mut ValidationReport,
    ) {
        let target = format!(
            "{} {} {}",
            relation.subject, relation.predicate, relation.object
        );

        if !VALID_RELATIONS.contains(&relation.predicate.as_str()) {
            report.issues.push(ValidationIssue {
                severity: Severity::Error,
                target: target.clone(),
                message: format!("未知的关系谓词: {}", relation.predicate),
            });
        }

        if kg.get_entity(&relation.subject).is_none() {
            report.issues.push(ValidationIssue {
                severity: Severity::Error,
                target: target.clone(),
                message: format!("关系主体不存在: {}", relation.subject),
            });
        }

        if kg.get_entity(&relation.object).is_none() {
            report.issues.push(ValidationIssue {
                severity: Severity::Error,
                target: target.clone(),
                message: format!("关系客体不存在: {}", relation.object),
            });
        }

        if self.require_relation_meta {
            if relation.meta.source.is_empty() {
                report.issues.push(ValidationIssue {
                    severity: Severity::Error,
                    target: target.clone(),
                    message: "关系缺少 ex:source".into(),
                });
            }

            if let Some(c) = relation.meta.confidence
                && !(0.0..=1.0).contains(&c)
            {
                report.issues.push(ValidationIssue {
                    severity: Severity::Error,
                    target: target.clone(),
                    message: format!("ex:confidence 越界: {}", c),
                });
            }
        }
    }
}
