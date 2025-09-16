//! # 国际标准规范 / International Standards Specifications
//!
//! 本模块定义了工作流系统应遵循的国际标准和规范，
//! 包括 ISO/IEC 标准、IEEE 标准、W3C 标准等。
//!
//! This module defines international standards and specifications that workflow
//! systems should follow, including ISO/IEC standards, IEEE standards, W3C standards, etc.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 工作流标准 / Workflow Standard
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowStandard {
    pub id: String,
    pub name: String,
    pub version: String,
    pub organization: String,
    pub description: String,
    pub requirements: Vec<StandardRequirement>,
    pub compliance_criteria: Vec<ComplianceCriteria>,
}

/// 标准要求 / Standard Requirement
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StandardRequirement {
    pub id: String,
    pub title: String,
    pub description: String,
    pub priority: RequirementPriority,
    pub category: RequirementCategory,
}

/// 要求优先级 / Requirement Priority
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum RequirementPriority {
    Must,
    Should,
    May,
    Optional,
}

/// 要求类别 / Requirement Category
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum RequirementCategory {
    Functional,
    NonFunctional,
    Security,
    Performance,
    Usability,
    Reliability,
    Maintainability,
    Portability,
}

/// 合规性标准 / Compliance Criteria
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplianceCriteria {
    pub id: String,
    pub description: String,
    pub test_method: String,
    pub pass_criteria: String,
    pub measurement_unit: Option<String>,
}

/// 国际工作流标准集合 / International Workflow Standards Collection
pub struct InternationalWorkflowStandards {
    standards: HashMap<String, WorkflowStandard>,
}

impl Default for InternationalWorkflowStandards {
    fn default() -> Self {
        Self::new()
    }
}

impl InternationalWorkflowStandards {
    /// 创建新的标准集合 / Create new standards collection
    pub fn new() -> Self {
        let mut standards = HashMap::new();

        // ISO/IEC 25010 - 软件质量模型 / Software Quality Model
        standards.insert("ISO_IEC_25010".to_string(), Self::iso_iec_25010());

        // IEEE 830 - 软件需求规格说明 / Software Requirements Specification
        standards.insert("IEEE_830".to_string(), Self::ieee_830());

        // W3C Web 标准 / W3C Web Standards
        standards.insert("W3C_WEB".to_string(), Self::w3c_web_standards());

        // RFC 2119 - 关键词使用 / Key Words for Use in RFCs
        standards.insert("RFC_2119".to_string(), Self::rfc_2119());

        Self { standards }
    }

    /// ISO/IEC 25010 软件质量模型 / ISO/IEC 25010 Software Quality Model
    fn iso_iec_25010() -> WorkflowStandard {
        WorkflowStandard {
            id: "ISO_IEC_25010".to_string(),
            name: "ISO/IEC 25010 Software Quality Model".to_string(),
            version: "2011".to_string(),
            organization: "ISO/IEC".to_string(),
            description: "软件产品质量模型，定义了软件质量的八个特性".to_string(),
            requirements: vec![
                StandardRequirement {
                    id: "FUNC_001".to_string(),
                    title: "功能适合性".to_string(),
                    description: "软件产品在指定条件下使用时，提供满足明确和隐含要求的功能的能力"
                        .to_string(),
                    priority: RequirementPriority::Must,
                    category: RequirementCategory::Functional,
                },
                StandardRequirement {
                    id: "PERF_001".to_string(),
                    title: "性能效率".to_string(),
                    description: "软件产品在指定条件下使用时，提供适当的性能的能力".to_string(),
                    priority: RequirementPriority::Must,
                    category: RequirementCategory::Performance,
                },
                StandardRequirement {
                    id: "SEC_001".to_string(),
                    title: "安全性".to_string(),
                    description: "软件产品保护信息和数据的能力".to_string(),
                    priority: RequirementPriority::Must,
                    category: RequirementCategory::Security,
                },
            ],
            compliance_criteria: vec![ComplianceCriteria {
                id: "CC_001".to_string(),
                description: "功能完整性测试".to_string(),
                test_method: "黑盒测试".to_string(),
                pass_criteria: "所有功能按预期工作".to_string(),
                measurement_unit: Some("%".to_string()),
            }],
        }
    }

    /// IEEE 830 软件需求规格说明 / IEEE 830 Software Requirements Specification
    fn ieee_830() -> WorkflowStandard {
        WorkflowStandard {
            id: "IEEE_830".to_string(),
            name: "IEEE 830 Software Requirements Specification".to_string(),
            version: "1998".to_string(),
            organization: "IEEE".to_string(),
            description: "软件需求规格说明的推荐实践".to_string(),
            requirements: vec![
                StandardRequirement {
                    id: "REQ_001".to_string(),
                    title: "需求完整性".to_string(),
                    description: "所有需求都应该被完整地定义和记录".to_string(),
                    priority: RequirementPriority::Must,
                    category: RequirementCategory::Functional,
                },
                StandardRequirement {
                    id: "REQ_002".to_string(),
                    title: "需求一致性".to_string(),
                    description: "需求之间不应该存在冲突".to_string(),
                    priority: RequirementPriority::Must,
                    category: RequirementCategory::Functional,
                },
            ],
            compliance_criteria: vec![ComplianceCriteria {
                id: "CC_002".to_string(),
                description: "需求可追溯性".to_string(),
                test_method: "需求追踪矩阵".to_string(),
                pass_criteria: "100% 需求可追溯".to_string(),
                measurement_unit: Some("%".to_string()),
            }],
        }
    }

    /// W3C Web 标准 / W3C Web Standards
    fn w3c_web_standards() -> WorkflowStandard {
        WorkflowStandard {
            id: "W3C_WEB".to_string(),
            name: "W3C Web Standards".to_string(),
            version: "2025".to_string(),
            organization: "W3C".to_string(),
            description: "Web 技术的国际标准".to_string(),
            requirements: vec![
                StandardRequirement {
                    id: "WEB_001".to_string(),
                    title: "可访问性".to_string(),
                    description: "Web 内容可访问性指南 (WCAG)".to_string(),
                    priority: RequirementPriority::Should,
                    category: RequirementCategory::Usability,
                },
                StandardRequirement {
                    id: "WEB_002".to_string(),
                    title: "语义化".to_string(),
                    description: "使用语义化的 HTML 标记".to_string(),
                    priority: RequirementPriority::Should,
                    category: RequirementCategory::Usability,
                },
            ],
            compliance_criteria: vec![ComplianceCriteria {
                id: "CC_003".to_string(),
                description: "WCAG 2.1 AA 合规性".to_string(),
                test_method: "自动化可访问性测试".to_string(),
                pass_criteria: "通过所有 AA 级别测试".to_string(),
                measurement_unit: None,
            }],
        }
    }

    /// RFC 2119 关键词使用 / RFC 2119 Key Words for Use in RFCs
    fn rfc_2119() -> WorkflowStandard {
        WorkflowStandard {
            id: "RFC_2119".to_string(),
            name: "RFC 2119 Key Words for Use in RFCs".to_string(),
            version: "1997".to_string(),
            organization: "IETF".to_string(),
            description: "RFC 文档中关键词的使用规范".to_string(),
            requirements: vec![StandardRequirement {
                id: "RFC_001".to_string(),
                title: "关键词一致性".to_string(),
                description: "使用 MUST、SHOULD、MAY 等关键词时保持一致性".to_string(),
                priority: RequirementPriority::Should,
                category: RequirementCategory::Functional,
            }],
            compliance_criteria: vec![ComplianceCriteria {
                id: "CC_004".to_string(),
                description: "关键词使用检查".to_string(),
                test_method: "文档审查".to_string(),
                pass_criteria: "关键词使用符合 RFC 2119".to_string(),
                measurement_unit: None,
            }],
        }
    }

    /// 获取所有标准 / Get all standards
    pub fn get_all_standards(&self) -> Vec<&WorkflowStandard> {
        self.standards.values().collect()
    }

    /// 根据 ID 获取标准 / Get standard by ID
    pub fn get_standard(&self, id: &str) -> Option<&WorkflowStandard> {
        self.standards.get(id)
    }

    /// 检查合规性 / Check compliance
    pub fn check_compliance(&self, implementation: &WorkflowImplementation) -> ComplianceReport {
        let mut report = ComplianceReport {
            overall_score: 0.0,
            standard_reports: Vec::new(),
            recommendations: Vec::new(),
        };

        for (standard_id, standard) in &self.standards {
            let standard_score = self.calculate_standard_score(standard, implementation);
            report.standard_reports.push(StandardComplianceReport {
                standard_id: standard_id.clone(),
                score: standard_score,
                passed_requirements: self.count_passed_requirements(standard, implementation),
                total_requirements: standard.requirements.len(),
            });
        }

        // 计算总体分数 / Calculate overall score
        if !report.standard_reports.is_empty() {
            report.overall_score = report.standard_reports.iter().map(|r| r.score).sum::<f64>()
                / report.standard_reports.len() as f64;
        }

        // 生成建议 / Generate recommendations
        report.recommendations = self.generate_recommendations(&report);

        report
    }

    /// 计算标准分数 / Calculate standard score
    fn calculate_standard_score(
        &self,
        standard: &WorkflowStandard,
        implementation: &WorkflowImplementation,
    ) -> f64 {
        let mut score = 0.0;
        let mut total_weight = 0.0;

        for requirement in &standard.requirements {
            let weight = match requirement.priority {
                RequirementPriority::Must => 4.0,
                RequirementPriority::Should => 3.0,
                RequirementPriority::May => 2.0,
                RequirementPriority::Optional => 1.0,
            };

            if implementation.meets_requirement(&requirement.id) {
                score += weight;
            }

            total_weight += weight;
        }

        if total_weight > 0.0 {
            (score / total_weight) * 100.0
        } else {
            0.0
        }
    }

    /// 计算通过的请求数量 / Count passed requirements
    fn count_passed_requirements(
        &self,
        standard: &WorkflowStandard,
        implementation: &WorkflowImplementation,
    ) -> usize {
        standard
            .requirements
            .iter()
            .filter(|req| implementation.meets_requirement(&req.id))
            .count()
    }

    /// 生成建议 / Generate recommendations
    fn generate_recommendations(&self, report: &ComplianceReport) -> Vec<String> {
        let mut recommendations = Vec::new();

        for standard_report in &report.standard_reports {
            if standard_report.score < 80.0 {
                recommendations.push(format!(
                    "改进 {} 标准的合规性，当前分数: {:.1}%",
                    standard_report.standard_id, standard_report.score
                ));
            }
        }

        if report.overall_score < 90.0 {
            recommendations.push("整体合规性需要改进，建议优先处理 MUST 级别的需求".to_string());
        }

        recommendations
    }
}

/// 工作流实现 / Workflow Implementation
pub struct WorkflowImplementation {
    features: HashMap<String, bool>,
}

impl Default for WorkflowImplementation {
    fn default() -> Self {
        Self::new()
    }
}

impl WorkflowImplementation {
    /// 创建新的实现 / Create new implementation
    pub fn new() -> Self {
        Self {
            features: HashMap::new(),
        }
    }

    /// 添加特性 / Add feature
    pub fn add_feature(&mut self, feature_id: String, implemented: bool) {
        self.features.insert(feature_id, implemented);
    }

    /// 检查是否满足需求 / Check if requirement is met
    pub fn meets_requirement(&self, requirement_id: &str) -> bool {
        self.features.get(requirement_id).copied().unwrap_or(false)
    }
}

/// 合规性报告 / Compliance Report
#[derive(Debug, Clone)]
pub struct ComplianceReport {
    pub overall_score: f64,
    pub standard_reports: Vec<StandardComplianceReport>,
    pub recommendations: Vec<String>,
}

/// 标准合规性报告 / Standard Compliance Report
#[derive(Debug, Clone)]
pub struct StandardComplianceReport {
    pub standard_id: String,
    pub score: f64,
    pub passed_requirements: usize,
    pub total_requirements: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_international_standards() {
        let standards = InternationalWorkflowStandards::new();
        let all_standards = standards.get_all_standards();

        assert!(!all_standards.is_empty());
        assert!(all_standards.len() >= 4); // ISO, IEEE, W3C, RFC
    }

    #[test]
    fn test_iso_iec_25010() {
        let standards = InternationalWorkflowStandards::new();
        let iso_standard = standards.get_standard("ISO_IEC_25010").unwrap();

        assert_eq!(iso_standard.id, "ISO_IEC_25010");
        assert_eq!(iso_standard.organization, "ISO/IEC");
        assert!(!iso_standard.requirements.is_empty());
    }

    #[test]
    fn test_compliance_check() {
        let standards = InternationalWorkflowStandards::new();
        let mut implementation = WorkflowImplementation::new();

        // 添加一些特性 / Add some features
        implementation.add_feature("FUNC_001".to_string(), true);
        implementation.add_feature("PERF_001".to_string(), true);
        implementation.add_feature("SEC_001".to_string(), false);

        let report = standards.check_compliance(&implementation);

        assert!(report.overall_score >= 0.0);
        assert!(report.overall_score <= 100.0);
        assert!(!report.standard_reports.is_empty());
    }
}
