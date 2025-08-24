# Rust形式化工程体系目录结构创建脚本

# 理论基础目录
$theoretical_dirs = @(
    "01_type_system", "02_memory_safety", "03_ownership_borrowing", 
    "04_concurrency_models", "05_trait_system", "06_lifetime_management",
    "07_error_handling", "08_macro_system", "09_formal_verification", 
    "10_mathematical_foundations"
)

# 编程范式目录
$paradigm_dirs = @(
    "01_synchronous", "02_asynchronous", "03_functional", "04_object_oriented",
    "05_concurrent", "06_parallel", "07_reactive", "08_event_driven",
    "09_actor_model", "10_data_oriented"
)

# 设计模式目录
$pattern_dirs = @(
    "01_creational", "02_structural", "03_behavioral", "04_concurrent",
    "05_parallel", "06_distributed", "07_workflow", "08_security",
    "09_performance", "10_rust_specific"
)

# 应用领域目录
$domain_dirs = @(
    "01_fintech", "02_game_development", "03_iot", "04_ai_ml",
    "05_blockchain_web3", "06_cloud_infrastructure", "07_big_data_analytics",
    "08_cybersecurity", "09_healthcare", "10_education_tech",
    "11_automotive", "12_ecommerce", "13_social_media", "14_enterprise", "15_mobile"
)

# 软件工程目录
$engineering_dirs = @(
    "01_architecture_design", "02_microservices", "03_service_mesh",
    "04_containerization", "05_devops", "06_cicd", "07_testing",
    "08_performance", "09_security", "10_quality"
)

# 工具链生态目录
$toolchain_dirs = @(
    "01_compiler", "02_package_manager", "03_build_tools", "04_testing_frameworks",
    "05_code_analysis", "06_performance_analysis", "07_security_tools",
    "08_ide_integration", "09_debugging", "10_monitoring"
)

# 跨语言比较目录
$comparison_dirs = @(
    "01_rust_vs_cpp", "02_rust_vs_go", "03_rust_vs_python", "04_rust_vs_js_ts",
    "05_rust_vs_java", "06_rust_vs_csharp", "07_rust_vs_swift", "08_rust_vs_kotlin",
    "09_rust_vs_zig", "10_rust_vs_nim"
)

# 实践示例目录
$example_dirs = @(
    "01_basic_examples", "02_advanced_examples", "03_real_world_cases",
    "04_performance_examples", "05_security_examples", "06_concurrent_examples",
    "07_async_examples", "08_web_examples", "09_system_examples", "10_embedded_examples"
)

# 研究议程目录
$research_dirs = @(
    "01_current_research", "02_future_directions", "03_open_problems",
    "04_research_methods", "05_publications", "06_conferences",
    "07_communities", "08_collaborations", "09_funding", "10_impact"
)

# 质量保证目录
$quality_dirs = @(
    "01_standards", "02_guidelines", "03_checklists", "04_validation",
    "05_testing", "06_review", "07_metrics", "08_automation", "09_monitoring", "10_improvement"
)

# 创建目录映射
$directory_mapping = @{
    "02_programming_paradigms" = $paradigm_dirs
    "03_design_patterns" = $pattern_dirs
    "04_application_domains" = $domain_dirs
    "05_software_engineering" = $engineering_dirs
    "06_toolchain_ecosystem" = $toolchain_dirs
    "07_cross_language_comparison" = $comparison_dirs
    "08_practical_examples" = $example_dirs
    "09_research_agenda" = $research_dirs
    "10_quality_assurance" = $quality_dirs
}

# 创建所有二级目录
foreach ($main_dir in $directory_mapping.Keys) {
    Write-Host "Creating directories in $main_dir..."
    foreach ($sub_dir in $directory_mapping[$main_dir]) {
        $path = Join-Path $main_dir $sub_dir
        if (!(Test-Path $path)) {
            New-Item -ItemType Directory -Path $path -Force | Out-Null
            Write-Host "  Created: $path"
        } else {
            Write-Host "  Exists: $path"
        }
    }
}

Write-Host "Directory structure creation completed!"
