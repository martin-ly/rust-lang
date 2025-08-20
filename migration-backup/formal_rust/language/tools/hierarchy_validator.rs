use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use regex::Regex;
use serde::{Deserialize, Serialize};

/// 层次定义
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Layer {
    pub name: String,
    pub description: String,
    pub modules: Vec<String>,
    pub requirements: Vec<String>,
    pub outputs: Vec<String>,
}

/// 模块定义
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Module {
    pub id: String,
    pub name: String,
    pub layer: String,
    pub dependencies: Vec<String>,
    pub concepts: Vec<String>,
    pub examples: Vec<String>,
}

/// 验证结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationResult {
    pub module_id: String,
    pub file_path: PathBuf,
    pub issue_type: IssueType,
    pub message: String,
    pub line: Option<usize>,
}

/// 问题类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum IssueType {
    LayerMismatch,
    MissingDependency,
    InvalidConcept,
    StructureViolation,
    NamingConvention,
}

/// 层次框架验证器
pub struct HierarchyValidator {
    pub layers: HashMap<String, Layer>,
    pub modules: HashMap<String, Module>,
    pub validation_results: Vec<ValidationResult>,
    pub layer_patterns: Vec<Regex>,
}

impl HierarchyValidator {
    /// 创建新的层次验证器
    pub fn new() -> Self {
        let mut validator = HierarchyValidator {
            layers: HashMap::new(),
            modules: HashMap::new(),
            validation_results: Vec::new(),
            layer_patterns: Vec::new(),
        };
        
        // 初始化层次框架
        validator.init_layers();
        validator.init_modules();
        validator.init_patterns();
        
        validator
    }
    
    /// 初始化四层理论框架
    fn init_layers(&mut self) {
        // 第一层：基础理论层
        self.layers.insert("第一层：基础理论层".to_string(), Layer {
            name: "第一层：基础理论层".to_string(),
            description: "数学和逻辑基础，为上层提供理论基础".to_string(),
            modules: vec![
                "集合论基础".to_string(),
                "逻辑系统".to_string(),
                "类型论基础".to_string(),
            ],
            requirements: vec![],
            outputs: vec![
                "形式化符号系统".to_string(),
                "逻辑推理规则".to_string(),
                "类型论基础".to_string(),
            ],
        });
        
        // 第二层：语言特性形式化层
        self.layers.insert("第二层：语言特性形式化层".to_string(), Layer {
            name: "第二层：语言特性形式化层".to_string(),
            description: "Rust语言特性的形式化定义和实现".to_string(),
            modules: vec![
                "所有权系统".to_string(),
                "类型系统".to_string(),
                "控制流".to_string(),
                "泛型系统".to_string(),
                "异步编程".to_string(),
            ],
            requirements: vec![
                "第一层：基础理论层".to_string(),
            ],
            outputs: vec![
                "语言特性形式化定义".to_string(),
                "代码示例库".to_string(),
                "实现规范".to_string(),
            ],
        });
        
        // 第三层：安全性与正确性证明层
        self.layers.insert("第三层：安全性与正确性证明层".to_string(), Layer {
            name: "第三层：安全性与正确性证明层".to_string(),
            description: "证明语言特性的安全性和正确性".to_string(),
            modules: vec![
                "内存安全".to_string(),
                "类型安全".to_string(),
                "并发安全".to_string(),
                "形式化验证".to_string(),
            ],
            requirements: vec![
                "第一层：基础理论层".to_string(),
                "第二层：语言特性形式化层".to_string(),
            ],
            outputs: vec![
                "安全性证明".to_string(),
                "正确性证明".to_string(),
                "验证工具".to_string(),
            ],
        });
        
        // 第四层：实践应用层
        self.layers.insert("第四层：实践应用层".to_string(), Layer {
            name: "第四层：实践应用层".to_string(),
            description: "在实际应用中的使用和最佳实践".to_string(),
            modules: vec![
                "系统编程".to_string(),
                "Web开发".to_string(),
                "嵌入式开发".to_string(),
                "区块链应用".to_string(),
                "机器学习".to_string(),
            ],
            requirements: vec![
                "第一层：基础理论层".to_string(),
                "第二层：语言特性形式化层".to_string(),
                "第三层：安全性与正确性证明层".to_string(),
            ],
            outputs: vec![
                "应用案例".to_string(),
                "最佳实践".to_string(),
                "性能指南".to_string(),
            ],
        });
    }
    
    /// 初始化模块定义
    fn init_modules(&mut self) {
        // 所有权系统模块
        self.modules.insert("01_ownership".to_string(), Module {
            id: "01_ownership".to_string(),
            name: "所有权系统".to_string(),
            layer: "第二层：语言特性形式化层".to_string(),
            dependencies: vec!["集合论基础".to_string()],
            concepts: vec![
                "01.01".to_string(), // 所有权定义
                "01.02".to_string(), // 借用系统
                "01.03".to_string(), // 所有权转移
                "01.05".to_string(), // 生命周期
            ],
            examples: vec![
                "01.01_ownership_definition.md".to_string(),
                "01.02_borrowing.md".to_string(),
                "01.03_ownership_transfer.md".to_string(),
                "01.05_lifetime.md".to_string(),
            ],
        });
        
        // 类型系统模块
        self.modules.insert("02_type_system".to_string(), Module {
            id: "02_type_system".to_string(),
            name: "类型系统".to_string(),
            layer: "第二层：语言特性形式化层".to_string(),
            dependencies: vec!["类型论基础".to_string()],
            concepts: vec![
                "02.01".to_string(), // 类型推断
                "02.02".to_string(), // 类型检查
                "02.03".to_string(), // 子类型
                "02.04".to_string(), // trait系统
            ],
            examples: vec![
                "02.01_type_inference.md".to_string(),
                "02.02_type_checking.md".to_string(),
                "02.03_subtyping.md".to_string(),
                "02.04_trait_system.md".to_string(),
            ],
        });
        
        // 控制流模块
        self.modules.insert("03_control_flow".to_string(), Module {
            id: "03_control_flow".to_string(),
            name: "控制流".to_string(),
            layer: "第二层：语言特性形式化层".to_string(),
            dependencies: vec!["逻辑系统".to_string()],
            concepts: vec![
                "03.01".to_string(), // 条件语句
                "03.02".to_string(), // 循环语句
                "03.03".to_string(), // 模式匹配
                "03.04".to_string(), // 错误处理
            ],
            examples: vec![
                "03.01_conditionals.md".to_string(),
                "03.02_loops.md".to_string(),
                "03.03_pattern_matching.md".to_string(),
                "03.04_error_handling.md".to_string(),
            ],
        });
    }
    
    /// 初始化验证模式
    fn init_patterns(&mut self) {
        let patterns = vec![
            r"layer\d+", // 层次标识
            r"module_\d+", // 模块标识
            r"concept_\d+\.\d+", // 概念标识
            r"example_\d+\.\d+", // 示例标识
        ];
        
        for pattern in patterns {
            if let Ok(regex) = Regex::new(pattern) {
                self.layer_patterns.push(regex);
            }
        }
    }
    
    /// 验证目录结构
    pub fn validate_directory_structure(&mut self, dir: &Path) -> Result<(), Box<dyn std::error::Error>> {
        self.validation_results.clear();
        
        // 检查层次目录
        for layer_name in self.layers.keys() {
            let layer_dir = dir.join(layer_name.replace("：", "_"));
            if !layer_dir.exists() {
                self.validation_results.push(ValidationResult {
                    module_id: layer_name.clone(),
                    file_path: layer_dir,
                    issue_type: IssueType::StructureViolation,
                    message: format!("缺少层次目录: {}", layer_name),
                    line: None,
                });
            }
        }
        
        // 检查模块目录
        for module in self.modules.values() {
            let module_dir = dir.join(&module.id);
            if !module_dir.exists() {
                self.validation_results.push(ValidationResult {
                    module_id: module.id.clone(),
                    file_path: module_dir,
                    issue_type: IssueType::StructureViolation,
                    message: format!("缺少模块目录: {}", module.id),
                    line: None,
                });
            }
        }
        
        // 检查示例文件
        for module in self.modules.values() {
            for example in &module.examples {
                let example_path = dir.join(&module.id).join(example);
                if !example_path.exists() {
                    self.validation_results.push(ValidationResult {
                        module_id: module.id.clone(),
                        file_path: example_path,
                        issue_type: IssueType::StructureViolation,
                        message: format!("缺少示例文件: {}", example),
                        line: None,
                    });
                }
            }
        }
        
        Ok(())
    }
    
    /// 验证文件内容
    pub fn validate_file_content(&mut self, path: &Path) -> Result<(), Box<dyn std::error::Error>> {
        let content = fs::read_to_string(path)?;
        let lines: Vec<&str> = content.lines().collect();
        
        for (line_num, line) in lines.iter().enumerate() {
            self.validate_line(path, line_num + 1, line);
        }
        
        Ok(())
    }
    
    /// 验证单行内容
    fn validate_line(&mut self, file: &Path, line_num: usize, line: &str) {
        // 检查层次标识
        if line.contains("理论层次") {
            let layer_match = self.find_layer_in_text(line);
            if let Some(layer) = layer_match {
                if !self.layers.contains_key(&layer) {
                    self.validation_results.push(ValidationResult {
                        module_id: "unknown".to_string(),
                        file_path: file.to_path_buf(),
                        issue_type: IssueType::LayerMismatch,
                        message: format!("无效的层次标识: {}", layer),
                        line: Some(line_num),
                    });
                }
            }
        }
        
        // 检查概念ID
        let concept_pattern = Regex::new(r"\d{2}\.\d{2}").unwrap();
        for mat in concept_pattern.find_iter(line) {
            let concept_id = mat.as_str();
            if !self.is_valid_concept_id(concept_id) {
                self.validation_results.push(ValidationResult {
                    module_id: "unknown".to_string(),
                    file_path: file.to_path_buf(),
                    issue_type: IssueType::InvalidConcept,
                    message: format!("无效的概念ID: {}", concept_id),
                    line: Some(line_num),
                });
            }
        }
        
        // 检查命名约定
        if line.contains("概念ID") || line.contains("概念名称") {
            if !line.contains("概念ID") || !line.contains("概念名称") {
                self.validation_results.push(ValidationResult {
                    module_id: "unknown".to_string(),
                    file_path: file.to_path_buf(),
                    issue_type: IssueType::NamingConvention,
                    message: "元数据格式不完整".to_string(),
                    line: Some(line_num),
                });
            }
        }
    }
    
    /// 在文本中查找层次标识
    fn find_layer_in_text(&self, text: &str) -> Option<String> {
        for layer_name in self.layers.keys() {
            if text.contains(layer_name) {
                return Some(layer_name.clone());
            }
        }
        None
    }
    
    /// 验证概念ID是否有效
    fn is_valid_concept_id(&self, concept_id: &str) -> bool {
        for module in self.modules.values() {
            if module.concepts.contains(&concept_id.to_string()) {
                return true;
            }
        }
        false
    }
    
    /// 验证层次依赖关系
    pub fn validate_dependencies(&self) -> Vec<ValidationResult> {
        let mut results = Vec::new();
        
        for module in self.modules.values() {
            let layer = self.layers.get(&module.layer);
            if let Some(layer) = layer {
                for dependency in &module.dependencies {
                    if !layer.requirements.contains(dependency) {
                        results.push(ValidationResult {
                            module_id: module.id.clone(),
                            file_path: PathBuf::new(),
                            issue_type: IssueType::MissingDependency,
                            message: format!("模块 {} 依赖了不在层次要求中的模块: {}", 
                                module.id, dependency),
                            line: None,
                        });
                    }
                }
            }
        }
        
        results
    }
    
    /// 生成验证报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        
        report.push_str("# 层次框架验证报告\n\n");
        report.push_str(&format!("验证时间: {}\n", chrono::Utc::now()));
        report.push_str(&format!("发现问题: {}\n", self.validation_results.len()));
        
        if self.validation_results.is_empty() {
            report.push_str("\n✅ 所有内容都符合层次框架要求！\n");
        } else {
            // 按问题类型分组
            let mut issues_by_type: HashMap<IssueType, Vec<&ValidationResult>> = HashMap::new();
            for result in &self.validation_results {
                issues_by_type.entry(result.issue_type.clone()).or_insert_with(Vec::new).push(result);
            }
            
            for (issue_type, results) in issues_by_type {
                report.push_str(&format!("\n## {:?} ({})\n\n", issue_type, results.len()));
                for result in results {
                    report.push_str(&format!("### 文件: {}\n", result.file_path.display()));
                    if let Some(line) = result.line {
                        report.push_str(&format!("行号: {}\n", line));
                    }
                    report.push_str(&format!("模块: {}\n", result.module_id));
                    report.push_str(&format!("问题: {}\n", result.message));
                    report.push_str("\n");
                }
            }
            
            report.push_str("## 建议\n\n");
            report.push_str("1. 检查目录结构是否符合层次框架要求\n");
            report.push_str("2. 确保所有概念ID都在定义范围内\n");
            report.push_str("3. 验证层次依赖关系是否正确\n");
            report.push_str("4. 检查命名约定是否一致\n");
        }
        
        report
    }
    
    /// 导出层次框架
    pub fn export_hierarchy(&self) -> String {
        let mut export = String::new();
        
        export.push_str("# Rust形式化理论四层框架\n\n");
        
        for layer in self.layers.values() {
            export.push_str(&format!("## {}\n\n", layer.name));
            export.push_str(&format!("**描述**: {}\n\n", layer.description));
            
            export.push_str("**模块**:\n");
            for module in &layer.modules {
                export.push_str(&format!("- {}\n", module));
            }
            export.push_str("\n");
            
            if !layer.requirements.is_empty() {
                export.push_str("**依赖**:\n");
                for req in &layer.requirements {
                    export.push_str(&format!("- {}\n", req));
                }
                export.push_str("\n");
            }
            
            if !layer.outputs.is_empty() {
                export.push_str("**输出**:\n");
                for output in &layer.outputs {
                    export.push_str(&format!("- {}\n", output));
                }
                export.push_str("\n");
            }
        }
        
        export
    }
}

/// 命令行接口
pub struct Cli {
    pub command: String,
    pub path: PathBuf,
    pub output: Option<PathBuf>,
}

impl Cli {
    pub fn parse_args() -> Result<Self, Box<dyn std::error::Error>> {
        let args: Vec<String> = std::env::args().collect();
        
        if args.len() < 3 {
            return Err("用法: hierarchy_validator <command> <path> [output]".into());
        }
        
        let command = args[1].clone();
        let path = PathBuf::from(&args[2]);
        let output = args.get(3).map(|s| PathBuf::from(s));
        
        Ok(Cli { command, path, output })
    }
    
    pub fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut validator = HierarchyValidator::new();
        
        match self.command.as_str() {
            "validate" => {
                validator.validate_directory_structure(&self.path)?;
                
                // 验证文件内容
                for entry in fs::read_dir(&self.path)? {
                    let entry = entry?;
                    let path = entry.path();
                    
                    if path.is_file() && path.extension().map_or(false, |ext| ext == "md") {
                        validator.validate_file_content(&path)?;
                    }
                }
                
                let report = validator.generate_report();
                
                if let Some(output_path) = &self.output {
                    fs::write(output_path, report)?;
                    println!("报告已保存到: {}", output_path.display());
                } else {
                    println!("{}", report);
                }
            }
            
            "export" => {
                let hierarchy = validator.export_hierarchy();
                
                if let Some(output_path) = &self.output {
                    fs::write(output_path, hierarchy)?;
                    println!("层次框架已导出到: {}", output_path.display());
                } else {
                    println!("{}", hierarchy);
                }
            }
            
            _ => {
                return Err(format!("未知命令: {}", self.command).into());
            }
        }
        
        Ok(())
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse_args()?;
    cli.run()
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;
    use std::fs;
    
    #[test]
    fn test_hierarchy_validator_creation() {
        let validator = HierarchyValidator::new();
        assert!(!validator.layers.is_empty());
        assert!(!validator.modules.is_empty());
        assert!(!validator.layer_patterns.is_empty());
    }
    
    #[test]
    fn test_layer_validation() {
        let validator = HierarchyValidator::new();
        
        // 测试有效层次
        assert!(validator.layers.contains_key("第一层：基础理论层"));
        assert!(validator.layers.contains_key("第二层：语言特性形式化层"));
        
        // 测试无效层次
        assert!(!validator.layers.contains_key("无效层次"));
    }
    
    #[test]
    fn test_concept_validation() {
        let validator = HierarchyValidator::new();
        
        // 测试有效概念ID
        assert!(validator.is_valid_concept_id("01.01"));
        assert!(validator.is_valid_concept_id("02.01"));
        
        // 测试无效概念ID
        assert!(!validator.is_valid_concept_id("99.99"));
    }
    
    #[test]
    fn test_dependency_validation() {
        let validator = HierarchyValidator::new();
        let results = validator.validate_dependencies();
        
        // 所有依赖都应该有效
        assert!(results.is_empty());
    }
} 