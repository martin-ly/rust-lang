//! 国际标准对标演示
//! 
//! 本示例展示了c18_model项目对标国际标准、著名大学课程和成熟度模型的功能。

use c18_model::{
    StandardComplianceChecker, ArchitectureStandard,
    CourseAlignmentAnalyzer, University, LearningPathPlanner,
    MaturityAssessor, MaturityModel,
    ArchitectureDescription as StandardsArchitectureDescription,
    ArchitectureViewpoint as StandardsArchitectureViewpoint,
    Concern as StandardsConcern,
    ConcernCategory,
};
use std::collections::HashMap;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== c18_model 国际标准对标演示 ===\n");

    // 1. 国际标准合规性检查演示
    demonstrate_standards_compliance()?;
    
    // 2. 大学课程对标分析演示
    demonstrate_university_course_alignment()?;
    
    // 3. 成熟度模型评估演示
    demonstrate_maturity_assessment()?;

    println!("=== 演示完成 ===");
    Ok(())
}

/// 演示国际标准合规性检查
fn demonstrate_standards_compliance() -> Result<(), Box<dyn std::error::Error>> {
    println!("1. 国际标准合规性检查演示");
    println!("{}", "=".repeat(40));

    // 创建标准合规性检查器
    let checker = StandardComplianceChecker::new();
    println!("支持的标准数量: {}", checker.get_supported_standards().len());
    
    // 显示所有支持的标准
    println!("\n支持的国际标准:");
    for standard in checker.get_supported_standards() {
        println!("  - {:?}", standard);
    }

    // 创建示例架构描述
    let architecture = StandardsArchitectureDescription {
        id: "demo_arch".to_string(),
        name: "演示架构".to_string(),
        version: "1.0.0".to_string(),
        viewpoints: vec![StandardsArchitectureViewpoint {
            id: "logical".to_string(),
            name: "逻辑视点".to_string(),
            description: "描述系统的功能分解和组件间的逻辑交互".to_string(),
            concerns: vec!["功能分解".to_string(), "组件交互".to_string()],
            stakeholders: vec!["架构师".to_string(), "开发人员".to_string()],
            model_kinds: vec![],
        }],
        views: vec![],
        models: vec![],
        concerns: vec![
            StandardsConcern {
                id: "performance".to_string(),
                name: "性能".to_string(),
                description: "系统响应时间和吞吐量要求".to_string(),
                category: ConcernCategory::NonFunctional,
            },
            StandardsConcern {
                id: "security".to_string(),
                name: "安全性".to_string(),
                description: "系统安全防护要求".to_string(),
                category: ConcernCategory::NonFunctional,
            },
        ],
        stakeholders: vec![],
    };

    // 检查ISO/IEC 25010合规性
    println!("\n检查ISO/IEC 25010合规性:");
    let result = checker.check_compliance(&architecture, ArchitectureStandard::ISO25010)?;
    println!("  合规性级别: {:?}", result.compliance_level);
    println!("  合规性分数: {:.1}%", result.score);
    println!("  问题数量: {}", result.issues.len());
    println!("  建议数量: {}", result.recommendations.len());

    // 检查ISO/IEC/IEEE 42010合规性
    println!("\n检查ISO/IEC/IEEE 42010合规性:");
    let result = checker.check_compliance(&architecture, ArchitectureStandard::ISO42010)?;
    println!("  合规性级别: {:?}", result.compliance_level);
    println!("  合规性分数: {:.1}%", result.score);

    println!();
    Ok(())
}

/// 演示大学课程对标分析
fn demonstrate_university_course_alignment() -> Result<(), Box<dyn std::error::Error>> {
    println!("2. 大学课程对标分析演示");
    println!("{}", "=".repeat(40));

    // 创建课程对标分析器
    let analyzer = CourseAlignmentAnalyzer::new();
    println!("支持的课程数量: {}", analyzer.get_all_courses().len());

    // 显示所有支持的大学
    println!("\n支持的大学:");
    let universities = [
        University::MIT, University::Harvard, University::Oxford, 
        University::TokyoUniversity, University::NUS
    ];
    
    for university in &universities {
        let courses = analyzer.get_courses_by_university(university.clone());
        println!("  - {:?}: {} 门课程", university, courses.len());
    }

    // 分析MIT 6.031课程
    println!("\n分析MIT 6.031课程:");
    let analysis = analyzer.analyze_alignment("MIT_6_031")?;
    println!("  课程名称: {}", analysis.course_name);
    println!("  对齐度分数: {:.1}%", analysis.alignment_score);
    println!("  总主题数: {}", analysis.total_topics);
    println!("  已映射主题数: {}", analysis.mapped_topics);
    println!("  Rust概念数: {}", analysis.rust_concepts.len());

    // 生成学习路径
    println!("\n生成MIT 6.031学习路径:");
    let planner = LearningPathPlanner::new();
    let path = planner.generate_learning_path("MIT_6_031")?;
    println!("  目标课程: {}", path.target_course);
    println!("  学习阶段数: {}", path.total_phases);
    println!("  预计总时长: {}", path.estimated_total_duration);
    
    for phase in &path.phases {
        println!("    阶段{}: {} - {}", phase.phase_number, phase.name, phase.estimated_duration);
    }

    println!();
    Ok(())
}

/// 演示成熟度模型评估
fn demonstrate_maturity_assessment() -> Result<(), Box<dyn std::error::Error>> {
    println!("3. 成熟度模型评估演示");
    println!("{}", "=".repeat(40));

    // 创建成熟度评估器
    let assessor = MaturityAssessor::new();
    println!("支持的成熟度模型数量: 4");

    // 显示所有支持的模型
    println!("\n支持的成熟度模型:");
    let models = [
        MaturityModel::CMMIDev,
        MaturityModel::P3M3,
        MaturityModel::MICOSE4aPS,
        MaturityModel::AssessITS,
    ];
    
    for model in &models {
        println!("  - {:?}", model);
    }

    // 准备评估证据
    let mut evidence = HashMap::new();
    evidence.insert("pp_1_1".to_string(), vec![
        "项目计划文档".to_string(),
        "进度跟踪记录".to_string(),
    ]);
    evidence.insert("req_1_1".to_string(), vec![
        "需求文档".to_string(),
        "需求评审记录".to_string(),
    ]);

    // 进行CMMI-DEV评估
    println!("\n进行CMMI-DEV评估:");
    let result = assessor.assess_maturity(MaturityModel::CMMIDev, &evidence)?;
    println!("  模型: {:?}", result.model);
    println!("  整体级别: {:?}", result.overall_level);
    println!("  整体分数: {:.1}%", result.score * 100.0);
    println!("  过程域数量: {}", result.process_areas.len());
    println!("  建议数量: {}", result.recommendations.len());
    println!("  下一步行动数量: {}", result.next_steps.len());

    // 显示过程域评估结果
    println!("\n过程域评估结果:");
    for (_id, assessment) in &result.process_areas {
        println!("  {}: 当前级别 {:?}, 分数 {:.1}%", 
                assessment.process_area.name, 
                assessment.current_level, 
                assessment.score * 100.0);
    }

    // 显示建议
    if !result.recommendations.is_empty() {
        println!("\n改进建议:");
        for (i, recommendation) in result.recommendations.iter().enumerate() {
            println!("  {}. {}", i + 1, recommendation);
        }
    }

    // 显示下一步行动
    if !result.next_steps.is_empty() {
        println!("\n下一步行动:");
        for (i, step) in result.next_steps.iter().enumerate() {
            println!("  {}. {}", i + 1, step);
        }
    }

    println!();
    Ok(())
}
