//! 综合示例：展示 c18_model 库的完整功能
//! 
//! 本示例展示了如何使用 c18_model 库进行：
//! 1. 国际标准合规性检查
//! 2. 大学课程对标分析
//! 3. 架构描述构建
//! 4. 学习路径规划

use c18_model::{
    StandardComplianceChecker, ArchitectureStandard,
    CourseAlignmentAnalyzer, LearningPathPlanner,
    ArchitectureDescription as StandardsArchitectureDescription,
    ArchitectureDescriptionBuilder as StandardsArchitectureDescriptionBuilder,
    ArchitectureViewpoint, ArchitectureView,
    ArchitectureModel, ArchitectureElement, ArchitectureRelationship,
    Concern, Stakeholder, ElementType, RelationshipType, ConcernCategory,
    Interface, InterfaceType, Operation, Parameter, ParameterDirection,
    ModelKind,
};
use std::collections::HashMap;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== c18_model 综合示例 ===\n");

    // 1. 创建架构描述
    println!("1. 创建架构描述...");
    let architecture = create_sample_architecture();
    println!("架构描述创建完成: {}", architecture.name);

    // 2. 进行标准合规性检查
    println!("\n2. 进行标准合规性检查...");
    let checker = StandardComplianceChecker::new();
    
    // 检查 ISO/IEC/IEEE 42010 合规性
    let iso_result = checker.check_compliance(&architecture, ArchitectureStandard::ISO42010)?;
    println!("ISO/IEC/IEEE 42010 合规性检查结果:");
    println!("  合规性级别: {:?}", iso_result.compliance_level);
    println!("  合规性分数: {:.1}%", iso_result.score);
    println!("  问题数量: {}", iso_result.issues.len());
    
    if !iso_result.issues.is_empty() {
        println!("  主要问题:");
        for issue in &iso_result.issues[..3] {
            println!("    - {:?}: {}", issue.severity, issue.description);
        }
    }

    // 3. 进行大学课程对标分析
    println!("\n3. 进行大学课程对标分析...");
    let analyzer = CourseAlignmentAnalyzer::new();
    
    // 分析 MIT 6.031 课程
    let mit_analysis = analyzer.analyze_alignment("MIT_6_031")?;
    println!("MIT 6.031 课程对标分析:");
    println!("  课程名称: {}", mit_analysis.course_name);
    println!("  对齐度分数: {:.1}%", mit_analysis.alignment_score);
    println!("  总主题数: {}", mit_analysis.total_topics);
    println!("  已映射主题数: {}", mit_analysis.mapped_topics);
    println!("  Rust 概念数: {}", mit_analysis.rust_concepts.len());

    // 4. 生成学习路径
    println!("\n4. 生成学习路径...");
    let planner = LearningPathPlanner::new();
    let learning_path = planner.generate_learning_path("MIT_6_031")?;
    
    println!("MIT 6.031 学习路径:");
    println!("  目标课程: {}", learning_path.target_course);
    println!("  大学: {:?}", learning_path.university);
    println!("  总阶段数: {}", learning_path.total_phases);
    println!("  预计总时长: {}", learning_path.estimated_total_duration);
    
    println!("\n  学习阶段:");
    for phase in &learning_path.phases {
        println!("    阶段 {}: {}", phase.phase_number, phase.name);
        println!("      描述: {}", phase.description);
        println!("      预计时长: {}", phase.estimated_duration);
        println!("      主题数量: {}", phase.topics.len());
    }

    // 5. 展示所有支持的课程
    println!("\n5. 支持的大学课程:");
    let all_courses = analyzer.get_all_courses();
    for course in all_courses {
        println!("  {:?} - {}: {}", course.university, course.course_code, course.course_name);
    }

    // 6. 展示所有支持的标准
    println!("\n6. 支持的架构标准:");
    let standards = checker.get_supported_standards();
    for standard in standards {
        println!("  {:?}", standard);
    }

    println!("\n=== 示例完成 ===");
    Ok(())
}

/// 创建示例架构描述
fn create_sample_architecture() -> StandardsArchitectureDescription {
    // 创建关注点
    let performance_concern = Concern {
        id: "performance".to_string(),
        name: "性能".to_string(),
        description: "系统性能要求".to_string(),
        category: ConcernCategory::NonFunctional,
    };

    let security_concern = Concern {
        id: "security".to_string(),
        name: "安全性".to_string(),
        description: "系统安全要求".to_string(),
        category: ConcernCategory::Quality,
    };

    // 创建利益相关者
    let developer = Stakeholder {
        id: "developer".to_string(),
        name: "开发人员".to_string(),
        role: "开发".to_string(),
        concerns: vec!["performance".to_string()],
    };

    let architect = Stakeholder {
        id: "architect".to_string(),
        name: "架构师".to_string(),
        role: "架构设计".to_string(),
        concerns: vec!["performance".to_string(), "security".to_string()],
    };

    // 创建模型类型
    let component_model_kind = ModelKind {
        id: "component_diagram".to_string(),
        name: "组件图".to_string(),
        description: "展示组件及其关系".to_string(),
        notation: "UML".to_string(),
    };

    // 创建视点
    let logical_viewpoint = ArchitectureViewpoint {
        id: "logical".to_string(),
        name: "逻辑视点".to_string(),
        description: "描述系统的功能分解和组件间的逻辑交互".to_string(),
        concerns: vec!["performance".to_string()],
        stakeholders: vec!["developer".to_string(), "architect".to_string()],
        model_kinds: vec![component_model_kind.clone()],
    };

    // 创建接口
    let user_interface = Interface {
        id: "user_interface".to_string(),
        name: "用户接口".to_string(),
        interface_type: InterfaceType::Provided,
        operations: vec![
            Operation {
                id: "get_user".to_string(),
                name: "get_user".to_string(),
                parameters: vec![
                    Parameter {
                        name: "user_id".to_string(),
                        parameter_type: "String".to_string(),
                        direction: ParameterDirection::In,
                    },
                ],
                return_type: Some("User".to_string()),
            },
        ],
    };

    // 创建架构元素
    let user_service = ArchitectureElement {
        id: "user_service".to_string(),
        name: "用户服务".to_string(),
        element_type: ElementType::Component,
        properties: {
            let mut props = HashMap::new();
            props.insert("language".to_string(), "Rust".to_string());
            props.insert("framework".to_string(), "Actix".to_string());
            props
        },
        interfaces: vec![user_interface],
    };

    let database = ArchitectureElement {
        id: "database".to_string(),
        name: "数据库".to_string(),
        element_type: ElementType::Component,
        properties: {
            let mut props = HashMap::new();
            props.insert("type".to_string(), "PostgreSQL".to_string());
            props.insert("version".to_string(), "13".to_string());
            props
        },
        interfaces: vec![],
    };

    // 创建架构关系
    let service_db_relationship = ArchitectureRelationship {
        id: "service_db_connection".to_string(),
        name: "服务数据库连接".to_string(),
        source: "user_service".to_string(),
        target: "database".to_string(),
        relationship_type: RelationshipType::Dependency,
        properties: {
            let mut props = HashMap::new();
            props.insert("protocol".to_string(), "TCP".to_string());
            props.insert("port".to_string(), "5432".to_string());
            props
        },
    };

    // 创建架构模型
    let logical_model = ArchitectureModel {
        id: "logical_model".to_string(),
        name: "逻辑模型".to_string(),
        model_kind: "component_diagram".to_string(),
        elements: vec![user_service, database],
        relationships: vec![service_db_relationship],
    };

    // 创建架构视图
    let logical_view = ArchitectureView {
        id: "logical_view".to_string(),
        name: "逻辑视图".to_string(),
        viewpoint_id: "logical".to_string(),
        models: vec!["logical_model".to_string()],
        description: "展示系统的功能组件和它们之间的交互关系".to_string(),
    };

    // 构建架构描述
    StandardsArchitectureDescriptionBuilder::new(
        "sample_architecture".to_string(),
        "示例架构".to_string(),
        "1.0.0".to_string(),
    )
    .add_viewpoint(logical_viewpoint)
    .add_view(logical_view)
    .add_model(logical_model)
    .add_concern(performance_concern)
    .add_concern(security_concern)
    .add_stakeholder(developer)
    .add_stakeholder(architect)
    .build()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_comprehensive_example() {
        // 测试架构描述创建
        let architecture = create_sample_architecture();
        assert_eq!(architecture.name, "示例架构");
        assert!(!architecture.viewpoints.is_empty());
        assert!(!architecture.views.is_empty());
        assert!(!architecture.models.is_empty());

        // 测试合规性检查
        let checker = StandardComplianceChecker::new();
        let result = checker.check_compliance(&architecture, ArchitectureStandard::ISO42010);
        assert!(result.is_ok());

        // 测试课程对标分析
        let analyzer = CourseAlignmentAnalyzer::new();
        let analysis = analyzer.analyze_alignment("MIT_6_031");
        assert!(analysis.is_ok());

        // 测试学习路径规划
        let planner = LearningPathPlanner::new();
        let path = planner.generate_learning_path("MIT_6_031");
        assert!(path.is_ok());
    }
}
