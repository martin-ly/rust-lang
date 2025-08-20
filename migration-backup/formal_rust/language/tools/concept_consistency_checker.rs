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
    pub symbol: String,
    pub level: u8,
    pub definition: String,
    pub examples: Vec<String>,
    pub related_concepts: Vec<String>,
}

/// 概念使用实例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConceptUsage {
    pub concept_id: String,
    pub file: PathBuf,
    pub line: usize,
    pub context: String,
    pub symbol_used: String,
    pub level_expected: u8,
    pub level_actual: u8,
}

/// 一致性检查结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConsistencyResult {
    pub concept_id: String,
    pub concept_name: String,
    pub violations: Vec<ConceptUsage>,
    pub consistency_score: f64,
    pub level: String,
}

/// 概念一致性检查器
pub struct ConceptConsistencyChecker {
    pub concepts: HashMap<String, Concept>,
    pub usage_patterns: Vec<Regex>,
    pub violations: Vec<ConceptUsage>,
    pub results: Vec<ConsistencyResult>,
}

impl ConceptConsistencyChecker {
    /// 创建新的概念一致性检查器
    pub fn new() -> Self {
        let mut checker = ConceptConsistencyChecker {
            concepts: HashMap::new(),
            usage_patterns: Vec::new(),
            violations: Vec::new(),
            results: Vec::new(),
        };
        
        // 初始化概念库
        checker.init_concepts();
        checker.init_patterns();
        
        checker
    }
    
    /// 初始化概念库
    fn init_concepts(&mut self) {
        // 第一层：基础理论层
        self.concepts.insert("01.01".to_string(), Concept {
            id: "01.01".to_string(),
            name: "集合论".to_string(),
            symbol: "𝕋, 𝕍, 𝕏".to_string(),
            level: 1,
            definition: "数学集合的基本理论".to_string(),
            examples: vec!["t ∈ 𝕋".to_string(), "v ∈ 𝕍".to_string()],
            related_concepts: vec!["01.02".to_string()],
        });
        
        self.concepts.insert("01.02".to_string(), Concept {
            id: "01.02".to_string(),
            name: "逻辑系统".to_string(),
            symbol: "∀, ∃, ⟹, ⟺".to_string(),
            level: 1,
            definition: "形式逻辑的基本系统".to_string(),
            examples: vec!["∀x. P(x)".to_string(), "P ⟹ Q".to_string()],
            related_concepts: vec!["01.01".to_string()],
        });
        
        // 第二层：语言特性形式化层
        self.concepts.insert("02.01".to_string(), Concept {
            id: "02.01".to_string(),
            name: "所有权".to_string(),
            symbol: "Own".to_string(),
            level: 2,
            definition: "Rust所有权系统的核心概念".to_string(),
            examples: vec!["Own(x, v)".to_string()],
            related_concepts: vec!["02.02".to_string(), "02.03".to_string()],
        });
        
        self.concepts.insert("02.02".to_string(), Concept {
            id: "02.02".to_string(),
            name: "借用".to_string(),
            symbol: "Borrow".to_string(),
            level: 2,
            definition: "Rust借用系统的核心概念".to_string(),
            examples: vec!["Borrow(r, x, α)".to_string()],
            related_concepts: vec!["02.01".to_string(), "02.03".to_string()],
        });
        
        self.concepts.insert("02.03".to_string(), Concept {
            id: "02.03".to_string(),
            name: "生命周期".to_string(),
            symbol: "Lifetime".to_string(),
            level: 2,
            definition: "Rust生命周期系统的核心概念".to_string(),
            examples: vec!["Lifetime(r) = [t₁, t₂]".to_string()],
            related_concepts: vec!["02.01".to_string(), "02.02".to_string()],
        });
        
        // 第三层：系统抽象层
        self.concepts.insert("03.01".to_string(), Concept {
            id: "03.01".to_string(),
            name: "并发系统".to_string(),
            symbol: "∥".to_string(),
            level: 3,
            definition: "并发执行的基本概念".to_string(),
            examples: vec!["P ∥ Q".to_string()],
            related_concepts: vec!["03.02".to_string()],
        });
        
        self.concepts.insert("03.02".to_string(), Concept {
            id: "03.02".to_string(),
            name: "同步关系".to_string(),
            symbol: "Sync".to_string(),
            level: 3,
            definition: "线程同步的基本概念".to_string(),
            examples: vec!["Sync(t₁, t₂)".to_string()],
            related_concepts: vec!["03.01".to_string()],
        });
        
        // 第四层：应用实践层
        self.concepts.insert("04.01".to_string(), Concept {
            id: "04.01".to_string(),
            name: "工厂模式".to_string(),
            symbol: "Factory".to_string(),
            level: 4,
            definition: "创建型设计模式".to_string(),
            examples: vec!["Factory(type, params)".to_string()],
            related_concepts: vec!["04.02".to_string()],
        });
        
        self.concepts.insert("04.02".to_string(), Concept {
            id: "04.02".to_string(),
            name: "观察者模式".to_string(),
            symbol: "Observer".to_string(),
            level: 4,
            definition: "行为型设计模式".to_string(),
            examples: vec!["Observer(subject, observer)".to_string()],
            related_concepts: vec!["04.01".to_string()],
        });
    }
    
    /// 初始化使用模式
    fn init_patterns(&mut self) {
        // 匹配概念使用的模式
        let patterns = vec![
            r"Own\([^)]+\)", // 所有权使用
            r"Borrow\([^)]+\)", // 借用使用
            r"Lifetime\([^)]+\)", // 生命周期使用
            r"Sync\([^)]+\)", // 同步使用
            r"Factory\([^)]+\)", // 工厂模式使用
            r"Observer\([^)]+\)", // 观察者模式使用
            r"𝕋|𝕍|𝕏", // 基础集合符号
            r"∀|∃|⟹|⟺", // 逻辑符号
            r"∥", // 并发符号
        ];
        
        for pattern in patterns {
            if let Ok(regex) = Regex::new(pattern) {
                self.usage_patterns.push(regex);
            }
        }
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
        for pattern in &self.usage_patterns {
            for capture in pattern.find_iter(line) {
                let symbol = capture.as_str();
                
                // 查找对应的概念
                for concept in self.concepts.values() {
                    if concept.symbol.contains(symbol) {
                        // 检查层次一致性
                        let expected_level = concept.level;
                        let actual_level = self.detect_level_from_context(line);
                        
                        if expected_level != actual_level {
                            self.violations.push(ConceptUsage {
                                concept_id: concept.id.clone(),
                                concept_name: concept.name.clone(),
                                file: file.to_path_buf(),
                                line: line_num,
                                context: line.to_string(),
                                symbol_used: symbol.to_string(),
                                level_expected: expected_level,
                                level_actual: actual_level,
                            });
                        }
                    }
                }
            }
        }
    }
    
    /// 从上下文检测层次
    fn detect_level_from_context(&self, context: &str) -> u8 {
        if context.contains("基础理论") || context.contains("数学") {
            1
        } else if context.contains("语言特性") || context.contains("所有权") || context.contains("类型") {
            2
        } else if context.contains("系统") || context.contains("并发") || context.contains("内存") {
            3
        } else if context.contains("应用") || context.contains("设计模式") || context.contains("框架") {
            4
        } else {
            0 // 未知层次
        }
    }
    
    /// 检查目录
    pub fn check_directory(&mut self, dir: &Path) -> Result<(), Box<dyn std::error::Error>> {
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
    
    /// 生成一致性报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        report.push_str("# 概念一致性检查报告\n\n");
        
        // 按概念分组统计
        let mut concept_violations: HashMap<String, Vec<&ConceptUsage>> = HashMap::new();
        for violation in &self.violations {
            concept_violations
                .entry(violation.concept_id.clone())
                .or_insert_with(Vec::new)
                .push(violation);
        }
        
        // 生成每个概念的检查结果
        for (concept_id, violations) in concept_violations {
            if let Some(concept) = self.concepts.get(&concept_id) {
                let consistency_score = if violations.is_empty() {
                    1.0
                } else {
                    1.0 - (violations.len() as f64 / 10.0).min(1.0)
                };
                
                let level_name = match concept.level {
                    1 => "基础理论层",
                    2 => "语言特性形式化层",
                    3 => "系统抽象层",
                    4 => "应用实践层",
                    _ => "未知层次",
                };
                
                report.push_str(&format!("## {}\n", concept.name));
                report.push_str(&format!("- **概念ID**: {}\n", concept.id));
                report.push_str(&format!("- **符号**: {}\n", concept.symbol));
                report.push_str(&format!("- **层次**: {}\n", level_name));
                report.push_str(&format!("- **一致性评分**: {:.2}\n", consistency_score));
                
                if !violations.is_empty() {
                    report.push_str("\n### 不一致使用\n\n");
                    for violation in violations {
                        report.push_str(&format!("- **文件**: {}\n", violation.file.display()));
                        report.push_str(&format!("  **行号**: {}\n", violation.line));
                        report.push_str(&format!("  **上下文**: {}\n", violation.context.trim()));
                        report.push_str(&format!("  **期望层次**: {}\n", violation.level_expected));
                        report.push_str(&format!("  **实际层次**: {}\n", violation.level_actual));
                        report.push_str("\n");
                    }
                } else {
                    report.push_str("\n✅ **一致性检查通过**\n\n");
                }
            }
        }
        
        // 总体统计
        let total_concepts = self.concepts.len();
        let concepts_with_violations = concept_violations.len();
        let total_violations = self.violations.len();
        
        report.push_str(&format!("\n## 总体统计\n\n"));
        report.push_str(&format!("- **总概念数**: {}\n", total_concepts));
        report.push_str(&format!("- **有问题的概念数**: {}\n", concepts_with_violations));
        report.push_str(&format!("- **总违规数**: {}\n", total_violations));
        report.push_str(&format!("- **整体一致性**: {:.2}%\n", 
            ((total_concepts - concepts_with_violations) as f64 / total_concepts as f64) * 100.0));
        
        report
    }
    
    /// 导出概念库
    pub fn export_concepts(&self) -> String {
        serde_json::to_string_pretty(&self.concepts).unwrap_or_default()
    }
}

/// 命令行接口
pub struct Cli {
    pub command: String,
    pub path: PathBuf,
    pub output: Option<PathBuf>,
}

impl Cli {
    /// 解析命令行参数
    pub fn parse_args() -> Result<Self, Box<dyn std::error::Error>> {
        let args: Vec<String> = std::env::args().collect();
        
        if args.len() < 3 {
            return Err("用法: concept-checker <command> <path> [output]".into());
        }
        
        let command = args[1].clone();
        let path = PathBuf::from(&args[2]);
        let output = if args.len() > 3 {
            Some(PathBuf::from(&args[3]))
        } else {
            None
        };
        
        Ok(Cli { command, path, output })
    }
    
    /// 运行检查
    pub fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut checker = ConceptConsistencyChecker::new();
        
        match self.command.as_str() {
            "check" => {
                if self.path.is_file() {
                    checker.check_file(&self.path)?;
                } else if self.path.is_dir() {
                    checker.check_directory(&self.path)?;
                } else {
                    return Err("路径不存在".into());
                }
                
                let report = checker.generate_report();
                
                if let Some(output_path) = &self.output {
                    fs::write(output_path, report)?;
                    println!("报告已保存到: {}", output_path.display());
                } else {
                    println!("{}", report);
                }
            },
            "export" => {
                let concepts = checker.export_concepts();
                
                if let Some(output_path) = &self.output {
                    fs::write(output_path, concepts)?;
                    println!("概念库已导出到: {}", output_path.display());
                } else {
                    println!("{}", concepts);
                }
            },
            _ => {
                return Err("未知命令".into());
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
    
    #[test]
    fn test_concept_checker_creation() {
        let checker = ConceptConsistencyChecker::new();
        assert!(!checker.concepts.is_empty());
        assert!(!checker.usage_patterns.is_empty());
    }
    
    #[test]
    fn test_concept_validation() {
        let mut checker = ConceptConsistencyChecker::new();
        
        // 测试正确的概念使用
        let correct_content = "在语言特性层中，我们使用 Own(x, v) 表示所有权关系。";
        checker.check_line(Path::new("test.md"), 1, correct_content);
        
        // 测试错误的概念使用
        let incorrect_content = "在基础理论层中，我们使用 Own(x, v) 表示所有权关系。";
        checker.check_line(Path::new("test.md"), 2, incorrect_content);
        
        assert!(!checker.violations.is_empty());
    }
    
    #[test]
    fn test_level_detection() {
        let checker = ConceptConsistencyChecker::new();
        
        assert_eq!(checker.detect_level_from_context("基础理论"), 1);
        assert_eq!(checker.detect_level_from_context("语言特性"), 2);
        assert_eq!(checker.detect_level_from_context("系统抽象"), 3);
        assert_eq!(checker.detect_level_from_context("应用实践"), 4);
    }
    
    #[test]
    fn test_report_generation() {
        let mut checker = ConceptConsistencyChecker::new();
        
        // 添加一些测试违规
        checker.violations.push(ConceptUsage {
            concept_id: "02.01".to_string(),
            concept_name: "所有权".to_string(),
            file: PathBuf::from("test.md"),
            line: 1,
            context: "测试内容".to_string(),
            symbol_used: "Own".to_string(),
            level_expected: 2,
            level_actual: 1,
        });
        
        let report = checker.generate_report();
        assert!(report.contains("概念一致性检查报告"));
        assert!(report.contains("所有权"));
    }
} 