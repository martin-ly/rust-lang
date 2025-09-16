//! # 工作流模式标准 / Workflow Pattern Standards
//!
//! 本模块定义了国际标准的工作流模式，包括 BPMN、XPDL 等标准模式，
//! 确保我们的实现符合行业标准。
//!
//! This module defines international standard workflow patterns, including BPMN, XPDL, etc.,
//! to ensure our implementation follows industry standards.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 工作流模式标准 / Workflow Pattern Standard
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowPatternStandard {
    pub standard_name: String,
    pub version: String,
    pub organization: String,
    pub patterns: Vec<WorkflowPattern>,
    pub compliance_level: ComplianceLevel,
}

/// 工作流模式 / Workflow Pattern
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowPattern {
    pub id: String,
    pub name: String,
    pub category: PatternCategory,
    pub description: String,
    pub elements: Vec<PatternElement>,
    pub rules: Vec<PatternRule>,
    pub examples: Vec<PatternExample>,
}

/// 模式类别 / Pattern Category
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum PatternCategory {
    ControlFlow,
    DataFlow,
    Resource,
    Exception,
    Communication,
    Integration,
}

/// 模式元素 / Pattern Element
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PatternElement {
    pub id: String,
    pub name: String,
    pub element_type: ElementType,
    pub properties: HashMap<String, String>,
    pub constraints: Vec<String>,
}

/// 元素类型 / Element Type
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum ElementType {
    StartEvent,
    EndEvent,
    Task,
    Gateway,
    SequenceFlow,
    DataObject,
    Pool,
    Lane,
    Message,
    Timer,
    Signal,
}

/// 模式规则 / Pattern Rule
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PatternRule {
    pub id: String,
    pub description: String,
    pub rule_type: RuleType,
    pub condition: String,
    pub action: String,
}

/// 规则类型 / Rule Type
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum RuleType {
    Validation,
    Execution,
    Transformation,
    Constraint,
}

/// 模式示例 / Pattern Example
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PatternExample {
    pub id: String,
    pub name: String,
    pub description: String,
    pub implementation: String,
    pub test_cases: Vec<TestCase>,
}

/// 测试用例 / Test Case
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestCase {
    pub id: String,
    pub name: String,
    pub input: String,
    pub expected_output: String,
    pub actual_output: Option<String>,
    pub status: TestStatus,
}

/// 测试状态 / Test Status
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum TestStatus {
    Passed,
    Failed,
    Pending,
    Skipped,
}

/// 合规性级别 / Compliance Level
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum ComplianceLevel {
    None,
    Partial,
    Full,
    Exceeds,
}

/// 国际模式库 / International Pattern Library
pub struct InternationalPatternLibrary {
    standards: HashMap<String, WorkflowPatternStandard>,
}

impl Default for InternationalPatternLibrary {
    fn default() -> Self {
        Self::new()
    }
}

impl InternationalPatternLibrary {
    /// 创建国际模式库 / Create international pattern library
    pub fn new() -> Self {
        let mut standards = HashMap::new();

        // BPMN 2.0 标准 / BPMN 2.0 Standard
        standards.insert("BPMN_2_0".to_string(), Self::bpmn_2_0_standard());

        // XPDL 2.2 标准 / XPDL 2.2 Standard
        standards.insert("XPDL_2_2".to_string(), Self::xpdl_2_2_standard());

        // BPEL 2.0 标准 / BPEL 2.0 Standard
        standards.insert("BPEL_2_0".to_string(), Self::bpel_2_0_standard());

        Self { standards }
    }

    /// BPMN 2.0 标准 / BPMN 2.0 Standard
    fn bpmn_2_0_standard() -> WorkflowPatternStandard {
        WorkflowPatternStandard {
            standard_name: "Business Process Model and Notation 2.0".to_string(),
            version: "2.0".to_string(),
            organization: "OMG".to_string(),
            patterns: vec![
                Self::sequence_pattern(),
                Self::parallel_gateway_pattern(),
                Self::exclusive_gateway_pattern(),
                Self::inclusive_gateway_pattern(),
                Self::event_based_gateway_pattern(),
                Self::subprocess_pattern(),
                Self::multi_instance_pattern(),
                Self::compensation_pattern(),
            ],
            compliance_level: ComplianceLevel::Full,
        }
    }

    /// 顺序模式 / Sequence Pattern
    fn sequence_pattern() -> WorkflowPattern {
        WorkflowPattern {
            id: "SEQ_001".to_string(),
            name: "Sequence Flow".to_string(),
            category: PatternCategory::ControlFlow,
            description: "表示活动之间的顺序执行关系".to_string(),
            elements: vec![
                PatternElement {
                    id: "ELEM_001".to_string(),
                    name: "Start Event".to_string(),
                    element_type: ElementType::StartEvent,
                    properties: HashMap::new(),
                    constraints: vec!["必须有且仅有一个开始事件".to_string()],
                },
                PatternElement {
                    id: "ELEM_002".to_string(),
                    name: "Task".to_string(),
                    element_type: ElementType::Task,
                    properties: HashMap::new(),
                    constraints: vec!["任务必须可执行".to_string()],
                },
                PatternElement {
                    id: "ELEM_003".to_string(),
                    name: "End Event".to_string(),
                    element_type: ElementType::EndEvent,
                    properties: HashMap::new(),
                    constraints: vec!["必须有且仅有一个结束事件".to_string()],
                },
            ],
            rules: vec![PatternRule {
                id: "RULE_001".to_string(),
                description: "顺序流规则".to_string(),
                rule_type: RuleType::Validation,
                condition: "前一个活动完成后才能执行下一个活动".to_string(),
                action: "按顺序执行活动".to_string(),
            }],
            examples: vec![PatternExample {
                id: "EX_001".to_string(),
                name: "简单顺序流程".to_string(),
                description: "订单处理流程：接收订单 -> 验证订单 -> 处理订单 -> 完成".to_string(),
                implementation: "使用 SequenceFlow 连接各个活动".to_string(),
                test_cases: vec![TestCase {
                    id: "TC_001".to_string(),
                    name: "正常顺序执行".to_string(),
                    input: "有效订单数据".to_string(),
                    expected_output: "订单处理完成".to_string(),
                    actual_output: None,
                    status: TestStatus::Pending,
                }],
            }],
        }
    }

    /// 并行网关模式 / Parallel Gateway Pattern
    fn parallel_gateway_pattern() -> WorkflowPattern {
        WorkflowPattern {
            id: "PAR_001".to_string(),
            name: "Parallel Gateway".to_string(),
            category: PatternCategory::ControlFlow,
            description: "表示活动的并行执行".to_string(),
            elements: vec![
                PatternElement {
                    id: "ELEM_004".to_string(),
                    name: "Parallel Gateway (Split)".to_string(),
                    element_type: ElementType::Gateway,
                    properties: HashMap::new(),
                    constraints: vec!["必须有两个或更多输出流".to_string()],
                },
                PatternElement {
                    id: "ELEM_005".to_string(),
                    name: "Parallel Gateway (Join)".to_string(),
                    element_type: ElementType::Gateway,
                    properties: HashMap::new(),
                    constraints: vec!["必须有两个或更多输入流".to_string()],
                },
            ],
            rules: vec![PatternRule {
                id: "RULE_002".to_string(),
                description: "并行执行规则".to_string(),
                rule_type: RuleType::Execution,
                condition: "所有输入流都完成后才能继续".to_string(),
                action: "并行执行所有输出流".to_string(),
            }],
            examples: vec![PatternExample {
                id: "EX_002".to_string(),
                name: "并行处理流程".to_string(),
                description: "订单处理：并行执行库存检查和支付验证".to_string(),
                implementation: "使用 ParallelGateway 分割和合并流程".to_string(),
                test_cases: vec![TestCase {
                    id: "TC_002".to_string(),
                    name: "并行执行测试".to_string(),
                    input: "订单数据".to_string(),
                    expected_output: "库存检查和支付验证并行完成".to_string(),
                    actual_output: None,
                    status: TestStatus::Pending,
                }],
            }],
        }
    }

    /// 排他网关模式 / Exclusive Gateway Pattern
    fn exclusive_gateway_pattern() -> WorkflowPattern {
        WorkflowPattern {
            id: "EXC_001".to_string(),
            name: "Exclusive Gateway".to_string(),
            category: PatternCategory::ControlFlow,
            description: "表示基于条件的路径选择".to_string(),
            elements: vec![PatternElement {
                id: "ELEM_006".to_string(),
                name: "Exclusive Gateway".to_string(),
                element_type: ElementType::Gateway,
                properties: HashMap::new(),
                constraints: vec!["必须有一个或多个输出流".to_string()],
            }],
            rules: vec![PatternRule {
                id: "RULE_003".to_string(),
                description: "排他选择规则".to_string(),
                rule_type: RuleType::Execution,
                condition: "只有一个条件为真的路径被执行".to_string(),
                action: "选择第一个为真的路径执行".to_string(),
            }],
            examples: vec![PatternExample {
                id: "EX_003".to_string(),
                name: "条件分支流程".to_string(),
                description: "根据订单金额选择不同的处理路径".to_string(),
                implementation: "使用 ExclusiveGateway 和条件表达式".to_string(),
                test_cases: vec![TestCase {
                    id: "TC_003".to_string(),
                    name: "条件分支测试".to_string(),
                    input: "高金额订单".to_string(),
                    expected_output: "走VIP处理路径".to_string(),
                    actual_output: None,
                    status: TestStatus::Pending,
                }],
            }],
        }
    }

    /// 包含网关模式 / Inclusive Gateway Pattern
    fn inclusive_gateway_pattern() -> WorkflowPattern {
        WorkflowPattern {
            id: "INC_001".to_string(),
            name: "Inclusive Gateway".to_string(),
            category: PatternCategory::ControlFlow,
            description: "表示基于条件的多路径选择".to_string(),
            elements: vec![PatternElement {
                id: "ELEM_007".to_string(),
                name: "Inclusive Gateway".to_string(),
                element_type: ElementType::Gateway,
                properties: HashMap::new(),
                constraints: vec!["可以有多个输出流同时执行".to_string()],
            }],
            rules: vec![PatternRule {
                id: "RULE_004".to_string(),
                description: "包含选择规则".to_string(),
                rule_type: RuleType::Execution,
                condition: "所有条件为真的路径都被执行".to_string(),
                action: "并行执行所有为真的路径".to_string(),
            }],
            examples: vec![PatternExample {
                id: "EX_004".to_string(),
                name: "多条件分支流程".to_string(),
                description: "根据客户类型和订单类型选择处理路径".to_string(),
                implementation: "使用 InclusiveGateway 和多个条件".to_string(),
                test_cases: vec![TestCase {
                    id: "TC_004".to_string(),
                    name: "多条件分支测试".to_string(),
                    input: "VIP客户的大订单".to_string(),
                    expected_output: "同时执行VIP处理和大订单处理".to_string(),
                    actual_output: None,
                    status: TestStatus::Pending,
                }],
            }],
        }
    }

    /// 基于事件的网关模式 / Event-based Gateway Pattern
    fn event_based_gateway_pattern() -> WorkflowPattern {
        WorkflowPattern {
            id: "EVT_001".to_string(),
            name: "Event-based Gateway".to_string(),
            category: PatternCategory::ControlFlow,
            description: "表示基于事件触发的路径选择".to_string(),
            elements: vec![PatternElement {
                id: "ELEM_008".to_string(),
                name: "Event-based Gateway".to_string(),
                element_type: ElementType::Gateway,
                properties: HashMap::new(),
                constraints: vec!["输出流必须连接到中间事件".to_string()],
            }],
            rules: vec![PatternRule {
                id: "RULE_005".to_string(),
                description: "事件触发规则".to_string(),
                rule_type: RuleType::Execution,
                condition: "第一个触发的事件决定执行路径".to_string(),
                action: "执行对应事件的路径".to_string(),
            }],
            examples: vec![PatternExample {
                id: "EX_005".to_string(),
                name: "事件驱动流程".to_string(),
                description: "等待用户确认或超时事件".to_string(),
                implementation: "使用 EventBasedGateway 和定时器事件".to_string(),
                test_cases: vec![TestCase {
                    id: "TC_005".to_string(),
                    name: "事件触发测试".to_string(),
                    input: "用户操作".to_string(),
                    expected_output: "根据用户操作执行对应路径".to_string(),
                    actual_output: None,
                    status: TestStatus::Pending,
                }],
            }],
        }
    }

    /// 子流程模式 / Subprocess Pattern
    fn subprocess_pattern() -> WorkflowPattern {
        WorkflowPattern {
            id: "SUB_001".to_string(),
            name: "Subprocess".to_string(),
            category: PatternCategory::ControlFlow,
            description: "表示嵌套的子流程".to_string(),
            elements: vec![PatternElement {
                id: "ELEM_009".to_string(),
                name: "Subprocess".to_string(),
                element_type: ElementType::Task,
                properties: HashMap::new(),
                constraints: vec!["子流程必须完整且可执行".to_string()],
            }],
            rules: vec![PatternRule {
                id: "RULE_006".to_string(),
                description: "子流程执行规则".to_string(),
                rule_type: RuleType::Execution,
                condition: "子流程必须完整执行".to_string(),
                action: "调用子流程并等待完成".to_string(),
            }],
            examples: vec![PatternExample {
                id: "EX_006".to_string(),
                name: "嵌套流程".to_string(),
                description: "订单处理包含支付子流程".to_string(),
                implementation: "使用 Subprocess 元素".to_string(),
                test_cases: vec![TestCase {
                    id: "TC_006".to_string(),
                    name: "子流程执行测试".to_string(),
                    input: "订单数据".to_string(),
                    expected_output: "子流程完整执行".to_string(),
                    actual_output: None,
                    status: TestStatus::Pending,
                }],
            }],
        }
    }

    /// 多实例模式 / Multi-instance Pattern
    fn multi_instance_pattern() -> WorkflowPattern {
        WorkflowPattern {
            id: "MUL_001".to_string(),
            name: "Multi-instance".to_string(),
            category: PatternCategory::ControlFlow,
            description: "表示活动的多次执行".to_string(),
            elements: vec![PatternElement {
                id: "ELEM_010".to_string(),
                name: "Multi-instance Task".to_string(),
                element_type: ElementType::Task,
                properties: HashMap::new(),
                constraints: vec!["必须指定实例数量或集合".to_string()],
            }],
            rules: vec![PatternRule {
                id: "RULE_007".to_string(),
                description: "多实例执行规则".to_string(),
                rule_type: RuleType::Execution,
                condition: "根据指定数量或集合创建实例".to_string(),
                action: "并行或顺序执行所有实例".to_string(),
            }],
            examples: vec![PatternExample {
                id: "EX_007".to_string(),
                name: "批量处理流程".to_string(),
                description: "批量处理多个订单项".to_string(),
                implementation: "使用 MultiInstance 标记".to_string(),
                test_cases: vec![TestCase {
                    id: "TC_007".to_string(),
                    name: "多实例执行测试".to_string(),
                    input: "订单项列表".to_string(),
                    expected_output: "所有订单项都被处理".to_string(),
                    actual_output: None,
                    status: TestStatus::Pending,
                }],
            }],
        }
    }

    /// 补偿模式 / Compensation Pattern
    fn compensation_pattern() -> WorkflowPattern {
        WorkflowPattern {
            id: "COM_001".to_string(),
            name: "Compensation".to_string(),
            category: PatternCategory::Exception,
            description: "表示异常情况下的补偿操作".to_string(),
            elements: vec![PatternElement {
                id: "ELEM_011".to_string(),
                name: "Compensation Task".to_string(),
                element_type: ElementType::Task,
                properties: HashMap::new(),
                constraints: vec!["补偿任务必须可逆".to_string()],
            }],
            rules: vec![PatternRule {
                id: "RULE_008".to_string(),
                description: "补偿执行规则".to_string(),
                rule_type: RuleType::Execution,
                condition: "异常发生时触发补偿".to_string(),
                action: "执行补偿操作恢复状态".to_string(),
            }],
            examples: vec![PatternExample {
                id: "EX_008".to_string(),
                name: "补偿流程".to_string(),
                description: "支付失败时取消订单".to_string(),
                implementation: "使用 Compensation 标记".to_string(),
                test_cases: vec![TestCase {
                    id: "TC_008".to_string(),
                    name: "补偿执行测试".to_string(),
                    input: "支付失败事件".to_string(),
                    expected_output: "订单被取消".to_string(),
                    actual_output: None,
                    status: TestStatus::Pending,
                }],
            }],
        }
    }

    /// XPDL 2.2 标准 / XPDL 2.2 Standard
    fn xpdl_2_2_standard() -> WorkflowPatternStandard {
        WorkflowPatternStandard {
            standard_name: "XML Process Definition Language 2.2".to_string(),
            version: "2.2".to_string(),
            organization: "WfMC".to_string(),
            patterns: vec![
                // XPDL 特定的模式
                Self::sequence_pattern(),
                Self::parallel_gateway_pattern(),
            ],
            compliance_level: ComplianceLevel::Partial,
        }
    }

    /// BPEL 2.0 标准 / BPEL 2.0 Standard
    fn bpel_2_0_standard() -> WorkflowPatternStandard {
        WorkflowPatternStandard {
            standard_name: "Business Process Execution Language 2.0".to_string(),
            version: "2.0".to_string(),
            organization: "OASIS".to_string(),
            patterns: vec![
                // BPEL 特定的模式
                Self::sequence_pattern(),
                Self::parallel_gateway_pattern(),
            ],
            compliance_level: ComplianceLevel::Partial,
        }
    }

    /// 获取所有标准 / Get all standards
    pub fn get_all_standards(&self) -> Vec<&WorkflowPatternStandard> {
        self.standards.values().collect()
    }

    /// 根据名称获取标准 / Get standard by name
    pub fn get_standard(&self, name: &str) -> Option<&WorkflowPatternStandard> {
        self.standards.get(name)
    }

    /// 检查模式合规性 / Check pattern compliance
    pub fn check_pattern_compliance(
        &self,
        pattern_id: &str,
        implementation: &PatternImplementation,
    ) -> PatternCompliance {
        let mut compliance = PatternCompliance {
            pattern_id: pattern_id.to_string(),
            compliance_score: 0.0,
            missing_elements: Vec::new(),
            missing_rules: Vec::new(),
            violations: Vec::new(),
            recommendations: Vec::new(),
        };

        // 查找模式 / Find pattern
        for standard in self.standards.values() {
            if let Some(pattern) = standard.patterns.iter().find(|p| p.id == pattern_id) {
                // 检查元素合规性 / Check element compliance
                for element in &pattern.elements {
                    if !implementation.has_element(&element.id) {
                        compliance.missing_elements.push(element.clone());
                    }
                }

                // 检查规则合规性 / Check rule compliance
                for rule in &pattern.rules {
                    if !implementation.satisfies_rule(&rule.id) {
                        compliance.missing_rules.push(rule.clone());
                    }
                }

                // 计算合规性分数 / Calculate compliance score
                let total_requirements = pattern.elements.len() + pattern.rules.len();
                let met_requirements = total_requirements
                    - compliance.missing_elements.len()
                    - compliance.missing_rules.len();

                if total_requirements > 0 {
                    compliance.compliance_score =
                        (met_requirements as f64 / total_requirements as f64) * 100.0;
                }

                // 生成建议 / Generate recommendations
                compliance.recommendations =
                    self.generate_pattern_recommendations(pattern, &compliance);

                break;
            }
        }

        compliance
    }

    /// 生成模式建议 / Generate pattern recommendations
    fn generate_pattern_recommendations(
        &self,
        pattern: &WorkflowPattern,
        compliance: &PatternCompliance,
    ) -> Vec<String> {
        let mut recommendations = Vec::new();

        if compliance.compliance_score < 80.0 {
            recommendations.push(format!(
                "模式 {} 的合规性需要改进，当前分数: {:.1}%",
                pattern.name, compliance.compliance_score
            ));
        }

        if !compliance.missing_elements.is_empty() {
            recommendations.push(format!(
                "缺少 {} 个必需元素，建议添加这些元素",
                compliance.missing_elements.len()
            ));
        }

        if !compliance.missing_rules.is_empty() {
            recommendations.push(format!(
                "缺少 {} 个必需规则，建议实现这些规则",
                compliance.missing_rules.len()
            ));
        }

        recommendations
    }
}

/// 模式实现 / Pattern Implementation
pub struct PatternImplementation {
    elements: std::collections::HashSet<String>,
    rules: std::collections::HashSet<String>,
}

impl Default for PatternImplementation {
    fn default() -> Self {
        Self::new()
    }
}

impl PatternImplementation {
    /// 创建模式实现 / Create pattern implementation
    pub fn new() -> Self {
        Self {
            elements: std::collections::HashSet::new(),
            rules: std::collections::HashSet::new(),
        }
    }

    /// 添加元素 / Add element
    pub fn add_element(&mut self, element_id: String) {
        self.elements.insert(element_id);
    }

    /// 添加规则 / Add rule
    pub fn add_rule(&mut self, rule_id: String) {
        self.rules.insert(rule_id);
    }

    /// 检查是否有元素 / Check if has element
    pub fn has_element(&self, element_id: &str) -> bool {
        self.elements.contains(element_id)
    }

    /// 检查是否满足规则 / Check if satisfies rule
    pub fn satisfies_rule(&self, rule_id: &str) -> bool {
        self.rules.contains(rule_id)
    }
}

/// 模式合规性 / Pattern Compliance
#[derive(Debug, Clone)]
pub struct PatternCompliance {
    pub pattern_id: String,
    pub compliance_score: f64,
    pub missing_elements: Vec<PatternElement>,
    pub missing_rules: Vec<PatternRule>,
    pub violations: Vec<String>,
    pub recommendations: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_international_pattern_library() {
        let library = InternationalPatternLibrary::new();
        let standards = library.get_all_standards();

        assert!(!standards.is_empty());
        assert!(standards.len() >= 3); // BPMN, XPDL, BPEL
    }

    #[test]
    fn test_bpmn_standard() {
        let library = InternationalPatternLibrary::new();
        let bpmn_standard = library.get_standard("BPMN_2_0").unwrap();

        assert_eq!(
            bpmn_standard.standard_name,
            "Business Process Model and Notation 2.0"
        );
        assert_eq!(bpmn_standard.organization, "OMG");
        assert!(!bpmn_standard.patterns.is_empty());
    }

    #[test]
    fn test_pattern_compliance() {
        let library = InternationalPatternLibrary::new();
        let mut implementation = PatternImplementation::new();

        // 添加一些元素和规则 / Add some elements and rules
        implementation.add_element("ELEM_001".to_string());
        implementation.add_rule("RULE_001".to_string());

        let compliance = library.check_pattern_compliance("SEQ_001", &implementation);

        assert_eq!(compliance.pattern_id, "SEQ_001");
        assert!(compliance.compliance_score >= 0.0);
        assert!(compliance.compliance_score <= 100.0);
    }

    #[test]
    fn test_workflow_patterns() {
        let library = InternationalPatternLibrary::new();
        let bpmn_standard = library.get_standard("BPMN_2_0").unwrap();

        // 检查关键模式是否存在 / Check if key patterns exist
        let pattern_ids: std::collections::HashSet<String> = bpmn_standard
            .patterns
            .iter()
            .map(|p| p.id.clone())
            .collect();

        assert!(pattern_ids.contains("SEQ_001")); // Sequence
        assert!(pattern_ids.contains("PAR_001")); // Parallel
        assert!(pattern_ids.contains("EXC_001")); // Exclusive
        assert!(pattern_ids.contains("INC_001")); // Inclusive
    }
}
