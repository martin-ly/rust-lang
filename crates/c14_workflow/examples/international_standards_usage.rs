//! # 国际标准对标使用示例 / International Standards Benchmarking Usage Example
//!
//! 本示例展示了如何使用 c14_workflow 的国际标准对标功能，
//! 包括标准合规性检查、大学课程对标、框架对标和性能基准测试。
//!
//! This example demonstrates how to use c14_workflow's international standards
//! benchmarking functionality, including standards compliance checking, university
//! course benchmarking, framework benchmarking, and performance benchmarking.

use c14_workflow::international_standards::performance_benchmarks::*;
use c14_workflow::international_standards::university_courses::*;
use c14_workflow::international_standards::workflow_patterns::*;
use c14_workflow::international_standards::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🌍 国际标准对标使用示例 / International Standards Benchmarking Usage Example");
    println!("{}", "=".repeat(80));

    // 1. 初始化国际标准模块 / Initialize international standards module
    println!("\n1. 初始化国际标准模块 / Initialize International Standards Module");
    c14_workflow::international_standards::init()?;

    // 2. 检查标准合规性 / Check standards compliance
    println!("\n2. 检查标准合规性 / Check Standards Compliance");
    let compliance = c14_workflow::international_standards::check_standards_compliance();
    println!("   合规性级别: {:?}", compliance.level);
    println!("   合规性分数: {:.1}%", compliance.compliance_score);
    println!("   支持的标准: {:?}", compliance.standards_met);

    // 3. 国际标准规范示例 / International Standards Specifications Example
    println!("\n3. 国际标准规范示例 / International Standards Specifications Example");
    let standards = InternationalWorkflowStandards::new();
    let all_standards = standards.get_all_standards();

    for standard in all_standards {
        println!(
            "   标准: {} v{} - {}",
            standard.name, standard.version, standard.organization
        );
        println!("     描述: {}", standard.description);
        println!("     要求数量: {}", standard.requirements.len());
        println!(
            "     合规性标准数量: {}",
            standard.compliance_criteria.len()
        );
    }

    // 4. 工作流模式标准示例 / Workflow Pattern Standards Example
    println!("\n4. 工作流模式标准示例 / Workflow Pattern Standards Example");
    let pattern_library = InternationalPatternLibrary::new();
    let bpmn_standard = pattern_library.get_standard("BPMN_2_0").unwrap();

    println!(
        "   BPMN 2.0 标准包含 {} 个模式:",
        bpmn_standard.patterns.len()
    );
    for pattern in &bpmn_standard.patterns {
        println!("     - {}: {}", pattern.name, pattern.description);
        println!("       类别: {:?}", pattern.category);
        println!("       元素数量: {}", pattern.elements.len());
        println!("       规则数量: {}", pattern.rules.len());
    }

    // 5. 大学课程对标示例 / University Course Benchmarking Example
    println!("\n5. 大学课程对标示例 / University Course Benchmarking Example");

    // MIT 课程对标 / MIT Course Benchmarking
    let mit_course = MITWorkflowCourse::new();
    let mit_benchmark = mit_course.get_benchmark();
    println!(
        "   MIT 课程: {} ({})",
        mit_benchmark.course_name, mit_benchmark.course_code
    );
    println!("     总学时: {} 小时", mit_benchmark.curriculum.total_hours);
    println!("     学分: {}", mit_benchmark.curriculum.credits);
    println!("     模块数量: {}", mit_benchmark.curriculum.modules.len());
    println!(
        "     学习成果数量: {}",
        mit_benchmark.learning_outcomes.len()
    );

    // Stanford 课程对标 / Stanford Course Benchmarking
    let stanford_course = StanfordWorkflowCourse::new();
    let stanford_benchmark = stanford_course.get_benchmark();
    println!(
        "   Stanford 课程: {} ({})",
        stanford_benchmark.course_name, stanford_benchmark.course_code
    );
    println!(
        "     总学时: {} 小时",
        stanford_benchmark.curriculum.total_hours
    );
    println!("     学分: {}", stanford_benchmark.curriculum.credits);
    println!(
        "     模块数量: {}",
        stanford_benchmark.curriculum.modules.len()
    );
    println!(
        "     学习成果数量: {}",
        stanford_benchmark.learning_outcomes.len()
    );

    // 课程对比分析 / Course Comparison Analysis
    let mut course_comparison = CourseComparison::new();
    course_comparison.add_course(mit_benchmark.clone());
    course_comparison.add_course(stanford_benchmark.clone());

    let comparison_report = course_comparison.generate_comparison_report();
    println!("   课程对比分析:");
    println!(
        "     共同主题数量: {}",
        comparison_report.common_topics.len()
    );
    println!(
        "     独特主题: {:?}",
        comparison_report.unique_topics.keys().collect::<Vec<_>>()
    );
    println!("     建议数量: {}", comparison_report.recommendations.len());

    // 6. 框架对标示例 / Framework Benchmarking Example
    println!("\n6. 框架对标示例 / Framework Benchmarking Example");

    // Temporal 框架对标 / Temporal Framework Benchmarking
    let mut temporal_benchmark = TemporalBenchmark::new();
    temporal_benchmark.run_benchmark().await?;
    let temporal_result = temporal_benchmark.get_benchmark();

    println!("   Temporal 框架基准测试:");
    println!("     版本: {}", temporal_result.version);
    println!(
        "     特性支持数量: {}",
        temporal_result.feature_comparison.features.len()
    );
    println!(
        "     吞吐量: {:.1} ops/sec",
        temporal_result.performance_metrics.throughput_ops_per_sec
    );
    println!(
        "     平均延迟: {:.1} ms",
        temporal_result.performance_metrics.average_latency_ms
    );
    println!(
        "     内存使用: {:.1} MB",
        temporal_result.performance_metrics.memory_usage_mb
    );

    // Cadence 框架对标 / Cadence Framework Benchmarking
    let mut cadence_benchmark = CadenceBenchmark::new();
    cadence_benchmark.run_benchmark().await?;
    let cadence_result = cadence_benchmark.get_benchmark();

    println!("   Cadence 框架基准测试:");
    println!("     版本: {}", cadence_result.version);
    println!(
        "     特性支持数量: {}",
        cadence_result.feature_comparison.features.len()
    );
    println!(
        "     吞吐量: {:.1} ops/sec",
        cadence_result.performance_metrics.throughput_ops_per_sec
    );
    println!(
        "     平均延迟: {:.1} ms",
        cadence_result.performance_metrics.average_latency_ms
    );
    println!(
        "     内存使用: {:.1} MB",
        cadence_result.performance_metrics.memory_usage_mb
    );

    // 框架对比分析 / Framework Comparison Analysis
    let mut framework_comparison = FrameworkComparison::new();
    framework_comparison.add_framework(temporal_result.clone());
    framework_comparison.add_framework(cadence_result.clone());

    let framework_report = framework_comparison.run_comparison().await?;
    println!("   框架对比分析:");
    println!("     获胜框架: {}", framework_report.winner);
    for framework in &framework_report.frameworks {
        println!(
            "     {} - 性能分数: {:.1}, 特性分数: {:.1}, 总体分数: {:.1}",
            framework.name,
            framework.performance_score,
            framework.feature_score,
            framework.overall_score
        );
    }

    // 7. 性能基准测试示例 / Performance Benchmarking Example
    println!("\n7. 性能基准测试示例 / Performance Benchmarking Example");

    let mut benchmark_suite = BenchmarkSuite::new();
    let standard_benchmarks = create_standard_benchmarks();

    for benchmark in standard_benchmarks {
        benchmark_suite.add_benchmark(benchmark);
    }

    let performance_report = benchmark_suite.run_all_benchmarks().await?;
    println!("   性能基准测试报告:");
    println!("     测试套件: {}", performance_report.suite_id);
    println!("     总体分数: {:.1}", performance_report.overall_score);
    println!(
        "     测试环境: {} 核心, {} GB 内存",
        performance_report.test_environment.cpu_cores,
        performance_report.test_environment.memory_gb
    );
    println!(
        "     基准测试数量: {}",
        performance_report.benchmark_results.len()
    );

    for result in &performance_report.benchmark_results {
        println!(
            "     {} - 分数: {:.1}",
            result.name, result.performance_score
        );
        println!(
            "       吞吐量: {:.1} ops/sec",
            result.overall_metrics.throughput_ops_per_sec
        );
        println!(
            "       平均延迟: {:.1} ms",
            result.overall_metrics.average_latency_ms
        );
        println!(
            "       内存使用: {:.1} MB",
            result.overall_metrics.memory_usage_mb
        );
        println!(
            "       CPU 使用: {:.1}%",
            result.overall_metrics.cpu_usage_percent
        );
        println!(
            "       错误率: {:.2}%",
            result.overall_metrics.error_rate_percent
        );
        println!(
            "       可用性: {:.2}%",
            result.overall_metrics.availability_percent
        );
    }

    // 8. 模式合规性检查示例 / Pattern Compliance Check Example
    println!("\n8. 模式合规性检查示例 / Pattern Compliance Check Example");

    let mut implementation = PatternImplementation::new();
    implementation.add_element("ELEM_001".to_string());
    implementation.add_element("ELEM_002".to_string());
    implementation.add_rule("RULE_001".to_string());

    let compliance_check = pattern_library.check_pattern_compliance("SEQ_001", &implementation);
    println!("   顺序模式合规性检查:");
    println!("     合规性分数: {:.1}%", compliance_check.compliance_score);
    println!(
        "     缺少元素数量: {}",
        compliance_check.missing_elements.len()
    );
    println!(
        "     缺少规则数量: {}",
        compliance_check.missing_rules.len()
    );
    println!("     建议数量: {}", compliance_check.recommendations.len());

    // 9. 总结和建议 / Summary and Recommendations
    println!("\n9. 总结和建议 / Summary and Recommendations");
    println!("   ✅ 国际标准合规性: {:?}", compliance.level);
    println!("   ✅ 支持的标准数量: {}", compliance.standards_met.len());
    println!("   ✅ 工作流模式数量: {}", bpmn_standard.patterns.len());
    println!("   ✅ 大学课程对标: MIT 和 Stanford");
    println!("   ✅ 框架对标: Temporal 和 Cadence");
    println!(
        "   ✅ 性能基准测试: {} 个测试场景",
        performance_report.benchmark_results.len()
    );

    println!("\n🎉 国际标准对标示例执行完成！");
    println!("🎉 International Standards Benchmarking Example Completed!");

    Ok(())
}
