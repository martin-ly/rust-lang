use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use regex::Regex;
use serde::{Deserialize, Serialize};

/// 概念定义
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Concept {
    pub id: String,
    pub name: String,
    pub definition: String,
    pub layer: String,
    pub related_concepts: Vec<String>,
    pub formal_definition: Option<String>,
    pub code_mapping: Option<String>,
}

/// 概念使用实例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConceptUsage {
    pub concept_id: String,
    pub file: PathBuf,
    pub line: usize,
    pub context: String,
    pub usage_type: UsageType,
}

/// 使用类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum UsageType {
    Definition,
    Reference,
    Example,
    CrossReference,
}

/// 概念一致性检查器
pub struct ConceptChecker {
    pub concepts: HashMap<String, Concept>,
    pub concept_patterns: Vec<Regex>,
    pub violations: Vec<ConceptUsage>,
    pub layer_hierarchy: HashMap<String, Vec<String>>,
}

impl ConceptChecker {
    /// 创建新的概念检查器
    pub fn new() -> Self {
        let mut checker = ConceptChecker {
            concepts: HashMap::new(),
            concept_patterns: Vec::new(),
            violations: Vec::new(),
            layer_hierarchy: HashMap::new(),
        };
        
        // 初始化概念系统
        checker.init_concepts();
        checker.init_patterns();
        checker.init_layer_hierarchy();
        
        checker
    }
    
    /// 初始化核心概念
    fn init_concepts(&mut self) {
        // 所有权系统概念
        self.concepts.insert("01.01".to_string(), Concept {
            id: "01.01".to_string(),
            name: "所有权定义".to_string(),
            definition: "变量拥有其绑定的值，负责管理内存".to_string(),
            layer: "第二层：语言特性形式化层".to_string(),
            related_concepts: vec!["01.02".to_string(), "01.03".to_string()],
            formal_definition: Some("Own(x, v) ≡ x ∈ 𝕏 ∧ v ∈ 𝕍 ∧ x ↦ v ∈ Σ".to_string()),
            code_mapping: Some("let x = value;".to_string()),
        });
        
        self.concepts.insert("01.02".to_string(), Concept {
            id: "01.02".to_string(),
            name: "借用系统".to_string(),
            definition: "通过引用临时访问值而不获取所有权".to_string(),
            layer: "第二层：语言特性形式化层".to_string(),
            related_concepts: vec!["01.01".to_string(), "01.05".to_string()],
            formal_definition: Some("Borrow(r, x, α) ≡ ∃v. Own(x, v) ∧ (r ↦ &^α v) ∈ Σ".to_string()),
            code_mapping: Some("let r = &x;".to_string()),
        });
        
        self.concepts.insert("01.03".to_string(), Concept {
            id: "01.03".to_string(),
            name: "所有权转移".to_string(),
            definition: "所有权从一个变量转移到另一个变量".to_string(),
            layer: "第二层：语言特性形式化层".to_string(),
            related_concepts: vec!["01.01".to_string(), "01.02".to_string()],
            formal_definition: Some("Move(x → y) ≡ Own(x, v) ∧ Transfer(x, y, v) ∧ ¬Own(x, v) ∧ Own(y, v)".to_string()),
            code_mapping: Some("let y = x;".to_string()),
        });
        
        // 类型系统概念
        self.concepts.insert("02.01".to_string(), Concept {
            id: "02.01".to_string(),
            name: "类型推断".to_string(),
            definition: "编译器自动推断表达式的类型".to_string(),
            layer: "第二层：语言特性形式化层".to_string(),
            related_concepts: vec!["02.02".to_string(), "02.03".to_string()],
            formal_definition: Some("Γ ⊢ e : T ≡ ∃σ. Unify(Γ, e, σ) ∧ T = σ(e)".to_string()),
            code_mapping: Some("let x = 42; // 推断为 i32".to_string()),
        });
        
        self.concepts.insert("02.02".to_string(), Concept {
            id: "02.02".to_string(),
            name: "类型检查".to_string(),
            definition: "验证表达式是否具有指定类型".to_string(),
            layer: "第二层：语言特性形式化层".to_string(),
            related_concepts: vec!["02.01".to_string(), "02.03".to_string()],
            formal_definition: Some("TypeCheck(Γ, e, T) ≡ Γ ⊢ e : T ∧ ValidType(T) ∧ Consistent(Γ, e, T)".to_string()),
            code_mapping: Some("let x: i32 = 42;".to_string()),
        });
        
        self.concepts.insert("02.03".to_string(), Concept {
            id: "02.03".to_string(),
            name: "子类型".to_string(),
            definition: "类型间的包含关系".to_string(),
            layer: "第二层：语言特性形式化层".to_string(),
            related_concepts: vec!["02.01".to_string(), "02.02".to_string()],
            formal_definition: Some("T <: U ≡ ∀e. Γ ⊢ e : T ⟹ Γ ⊢ e : U".to_string()),
            code_mapping: Some("fn accept_number(n: &dyn ToString)".to_string()),
        });
        
        // 生命周期概念
        self.concepts.insert("01.05".to_string(), Concept {
            id: "01.05".to_string(),
            name: "生命周期".to_string(),
            definition: "引用有效的持续时间".to_string(),
            layer: "第二层：语言特性形式化层".to_string(),
            related_concepts: vec!["01.02".to_string(), "01.01".to_string()],
            formal_definition: Some("Live(r, α) ≡ ∀t ∈ α. Valid(r, Σ_t) ∧ ¬Dangling(r, Σ_t)".to_string()),
            code_mapping: Some("fn longest<'a>(x: &'a str, y: &'a str) -> &'a str".to_string()),
        });
    }
    
    /// 初始化概念模式
    fn init_patterns(&mut self) {
        // 匹配概念ID的模式
        let patterns = vec![
            r"\d{2}\.\d{2}", // 概念ID格式：XX.XX
            r"Own\([^)]+\)", // 所有权关系
            r"Borrow\([^)]+\)", // 借用关系
            r"Move\([^)]+\)", // 移动关系
            r"Γ\s*⊢\s*[^:]+:\s*[A-Za-z]", // 类型判断
            r"<:", // 子类型关系
            r"Live\([^)]+\)", // 生命周期
        ];
        
        for pattern in patterns {
            if let Ok(regex) = Regex::new(pattern) {
                self.concept_patterns.push(regex);
            }
        }
    }
    
    /// 初始化层次结构
    fn init_layer_hierarchy(&mut self) {
        self.layer_hierarchy.insert("第一层：基础理论层".to_string(), vec![
            "集合论基础".to_string(),
            "逻辑系统".to_string(),
            "类型论基础".to_string(),
        ]);
        
        self.layer_hierarchy.insert("第二层：语言特性形式化层".to_string(), vec![
            "所有权系统".to_string(),
            "类型系统".to_string(),
            "控制流".to_string(),
            "泛型系统".to_string(),
        ]);
        
        self.layer_hierarchy.insert("第三层：安全性与正确性证明层".to_string(), vec![
            "内存安全".to_string(),
            "类型安全".to_string(),
            "并发安全".to_string(),
        ]);
        
        self.layer_hierarchy.insert("第四层：实践应用层".to_string(), vec![
            "系统编程".to_string(),
            "Web开发".to_string(),
            "嵌入式开发".to_string(),
        ]);
    }
    
    /// 检查单个文件
    pub fn check_file(&mut self, path: &Path) -> Result<(), Box<dyn std::error::Error>> {
        let content = fs::read_to_string(path)?;
        let lines: Vec<&str> = content.lines().collect();
        
        for (line_num, line) in lines.iter().enumerate() {
            self.check_line(path, line_num + 1, line);
        }
        
        Ok(())
    }
    
    /// 检查单行内容
    fn check_line(&mut self, file: &Path, line_num: usize, line: &str) {
        for pattern in &self.concept_patterns {
            for mat in pattern.find_iter(line) {
                let concept_text = mat.as_str();
                
                // 检查概念是否在定义系统中
                if !self.is_valid_concept_usage(concept_text) {
                    self.violations.push(ConceptUsage {
                        concept_id: concept_text.to_string(),
                        file: file.to_path_buf(),
                        line: line_num,
                        context: line.to_string(),
                        usage_type: UsageType::Reference,
                    });
                }
            }
        }
        
        // 检查概念ID的使用
        let concept_id_pattern = Regex::new(r"\d{2}\.\d{2}").unwrap();
        for mat in concept_id_pattern.find_iter(line) {
            let concept_id = mat.as_str();
            if !self.concepts.contains_key(concept_id) {
                self.violations.push(ConceptUsage {
                    concept_id: concept_id.to_string(),
                    file: file.to_path_buf(),
                    line: line_num,
                    context: line.to_string(),
                    usage_type: UsageType::Reference,
                });
            }
        }
    }
    
    /// 验证概念使用是否有效
    fn is_valid_concept_usage(&self, concept_text: &str) -> bool {
        // 检查是否是已知的概念定义
        for concept in self.concepts.values() {
            if concept_text.contains(&concept.id) || 
               concept_text.contains(&concept.name) ||
               (concept.formal_definition.is_some() && 
                concept_text.contains(concept.formal_definition.as_ref().unwrap())) {
                return true;
            }
        }
        false
    }
    
    /// 检查目录中的所有Markdown文件
    pub fn check_directory(&mut self, dir: &Path) -> Result<(), Box<dyn std::error::Error>> {
        self.violations.clear();
        
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            
            if path.is_file() && path.extension().map_or(false, |ext| ext == "md") {
                self.check_file(&path)?;
            } else if path.is_dir() {
                self.check_directory(&path)?;
            }
        }
        
        Ok(())
    }
    
    /// 检查概念层次一致性
    pub fn check_layer_consistency(&self) -> Vec<String> {
        let mut issues = Vec::new();
        
        for concept in self.concepts.values() {
            if !self.layer_hierarchy.contains_key(&concept.layer) {
                issues.push(format!("概念 {} 的层次 '{}' 不在层次框架中", 
                    concept.id, concept.layer));
            }
        }
        
        issues
    }
    
    /// 检查概念引用一致性
    pub fn check_reference_consistency(&self) -> Vec<String> {
        let mut issues = Vec::new();
        let valid_concept_ids: HashSet<String> = self.concepts.keys().cloned().collect();
        
        for concept in self.concepts.values() {
            for related_id in &concept.related_concepts {
                if !valid_concept_ids.contains(related_id) {
                    issues.push(format!("概念 {} 引用了不存在的概念 {}", 
                        concept.id, related_id));
                }
            }
        }
        
        issues
    }
    
    /// 生成检查报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        
        report.push_str("# 概念一致性检查报告\n\n");
        report.push_str(&format!("检查时间: {}\n", chrono::Utc::now()));
        report.push_str(&format!("发现违规: {}\n", self.violations.len()));
        
        // 层次一致性检查
        let layer_issues = self.check_layer_consistency();
        if !layer_issues.is_empty() {
            report.push_str(&format!("\n## 层次一致性问题 ({})\n\n", layer_issues.len()));
            for issue in layer_issues {
                report.push_str(&format!("- {}\n", issue));
            }
        }
        
        // 引用一致性检查
        let reference_issues = self.check_reference_consistency();
        if !reference_issues.is_empty() {
            report.push_str(&format!("\n## 引用一致性问题 ({})\n\n", reference_issues.len()));
            for issue in reference_issues {
                report.push_str(&format!("- {}\n", issue));
            }
        }
        
        if self.violations.is_empty() && layer_issues.is_empty() && reference_issues.is_empty() {
            report.push_str("\n✅ 所有概念使用都符合一致性要求！\n");
        } else {
            report.push_str("\n## 发现的违规\n\n");
            
            for violation in &self.violations {
                report.push_str(&format!("### 文件: {}\n", violation.file.display()));
                report.push_str(&format!("行号: {}\n", violation.line));
                report.push_str(&format!("概念: `{}`\n", violation.concept_id));
                report.push_str(&format!("上下文: `{}`\n", violation.context));
                report.push_str("\n");
            }
            
            report.push_str("## 建议\n\n");
            report.push_str("1. 检查上述概念是否应该添加到概念系统中\n");
            report.push_str("2. 确保概念定义与使用保持一致\n");
            report.push_str("3. 验证概念层次分类的正确性\n");
            report.push_str("4. 检查概念间的引用关系\n");
        }
        
        report
    }
    
    /// 导出概念系统
    pub fn export_concepts(&self) -> String {
        let mut export = String::new();
        
        export.push_str("# Rust形式化理论概念系统\n\n");
        
        // 按层次分组
        let mut layers: HashMap<String, Vec<&Concept>> = HashMap::new();
        for concept in self.concepts.values() {
            layers.entry(concept.layer.clone()).or_insert_with(Vec::new).push(concept);
        }
        
        for (layer, concepts) in layers {
            export.push_str(&format!("## {}\n\n", layer));
            export.push_str("| 概念ID | 概念名称 | 定义 | 相关概念 |\n");
            export.push_str("|--------|----------|------|----------|\n");
            
            for concept in concepts {
                let related = concept.related_concepts.join(", ");
                export.push_str(&format!("| {} | {} | {} | {} |\n", 
                    concept.id, concept.name, concept.definition, related));
            }
            
            export.push_str("\n");
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
            return Err("用法: concept_checker <command> <path> [output]".into());
        }
        
        let command = args[1].clone();
        let path = PathBuf::from(&args[2]);
        let output = args.get(3).map(|s| PathBuf::from(s));
        
        Ok(Cli { command, path, output })
    }
    
    pub fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut checker = ConceptChecker::new();
        
        match self.command.as_str() {
            "check" => {
                if self.path.is_file() {
                    checker.check_file(&self.path)?;
                } else {
                    checker.check_directory(&self.path)?;
                }
                
                let report = checker.generate_report();
                
                if let Some(output_path) = &self.output {
                    fs::write(output_path, report)?;
                    println!("报告已保存到: {}", output_path.display());
                } else {
                    println!("{}", report);
                }
            }
            
            "export" => {
                let concepts = checker.export_concepts();
                
                if let Some(output_path) = &self.output {
                    fs::write(output_path, concepts)?;
                    println!("概念系统已导出到: {}", output_path.display());
                } else {
                    println!("{}", concepts);
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
    fn test_concept_checker_creation() {
        let checker = ConceptChecker::new();
        assert!(!checker.concepts.is_empty());
        assert!(!checker.concept_patterns.is_empty());
        assert!(!checker.layer_hierarchy.is_empty());
    }
    
    #[test]
    fn test_concept_validation() {
        let checker = ConceptChecker::new();
        
        // 测试有效概念
        assert!(checker.concepts.contains_key("01.01"));
        assert!(checker.concepts.contains_key("02.01"));
        
        // 测试无效概念
        assert!(!checker.concepts.contains_key("99.99"));
    }
    
    #[test]
    fn test_file_checking() {
        let mut checker = ConceptChecker::new();
        let temp_dir = tempdir().unwrap();
        let test_file = temp_dir.path().join("test.md");
        
        // 创建测试文件
        let content = r#"
# 测试文档

这里使用了正确的概念: 01.01 (所有权定义)
这里使用了错误的概念: 99.99 (无效概念)

更多正确概念: Own(x, v), Borrow(r, x, α)
"#;
        
        fs::write(&test_file, content).unwrap();
        
        // 检查文件
        checker.check_file(&test_file).unwrap();
        
        // 应该发现一个违规
        assert_eq!(checker.violations.len(), 1);
        assert_eq!(checker.violations[0].concept_id, "99.99");
    }
    
    #[test]
    fn test_layer_consistency() {
        let checker = ConceptChecker::new();
        let issues = checker.check_layer_consistency();
        
        // 所有概念都应该在层次框架中
        assert!(issues.is_empty());
    }
    
    #[test]
    fn test_reference_consistency() {
        let checker = ConceptChecker::new();
        let issues = checker.check_reference_consistency();
        
        // 所有引用都应该指向存在的概念
        assert!(issues.is_empty());
    }
} 