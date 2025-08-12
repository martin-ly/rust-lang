use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::io::{self, Write};

#[derive(Debug)]
pub struct SectionInfo {
    pub name: String,
    pub level: usize,
    pub line_number: usize,
    pub content_length: usize,
}

#[derive(Debug)]
pub struct StructureReport {
    pub file_path: String,
    pub total_sections: usize,
    pub required_sections: Vec<String>,
    pub missing_sections: Vec<String>,
    pub optional_sections: Vec<String>,
    pub structure_score: f64,
    pub compliance_rate: f64,
    pub success: bool,
    pub error_message: Option<String>,
}

pub struct StructureChecker {
    pub required_sections: Vec<String>,
    pub optional_sections: Vec<String>,
    pub section_weights: HashMap<String, f64>,
}

impl StructureChecker {
    pub fn new() -> Self {
        let mut required_sections = Vec::new();
        required_sections.push("概述".to_string());
        required_sections.push("技术背景".to_string());
        required_sections.push("核心概念".to_string());
        required_sections.push("技术实现".to_string());
        required_sections.push("形式化分析".to_string());
        required_sections.push("应用案例".to_string());
        required_sections.push("性能分析".to_string());
        required_sections.push("最佳实践".to_string());
        required_sections.push("常见问题".to_string());
        required_sections.push("未来展望".to_string());
        
        let mut optional_sections = Vec::new();
        optional_sections.push("高级特性".to_string());
        optional_sections.push("扩展应用".to_string());
        optional_sections.push("社区反馈".to_string());
        optional_sections.push("相关链接".to_string());
        optional_sections.push("参考资料".to_string());
        
        let mut section_weights = HashMap::new();
        section_weights.insert("概述".to_string(), 0.10);
        section_weights.insert("技术背景".to_string(), 0.12);
        section_weights.insert("核心概念".to_string(), 0.15);
        section_weights.insert("技术实现".to_string(), 0.18);
        section_weights.insert("形式化分析".to_string(), 0.15);
        section_weights.insert("应用案例".to_string(), 0.12);
        section_weights.insert("性能分析".to_string(), 0.08);
        section_weights.insert("最佳实践".to_string(), 0.05);
        section_weights.insert("常见问题".to_string(), 0.03);
        section_weights.insert("未来展望".to_string(), 0.02);
        
        Self {
            required_sections,
            optional_sections,
            section_weights,
        }
    }
    
    pub fn check_document(&self, document_path: &Path) -> Result<StructureReport, io::Error> {
        let content = fs::read_to_string(document_path)?;
        
        let sections = self.extract_sections(&content);
        let mut found_sections = Vec::new();
        let mut missing_sections = Vec::new();
        
        // 检查必需章节
        for required_section in &self.required_sections {
            if sections.iter().any(|s| s.name.contains(required_section)) {
                found_sections.push(required_section.clone());
            } else {
                missing_sections.push(required_section.clone());
            }
        }
        
        // 计算结构分数
        let total_weight: f64 = self.section_weights.values().sum();
        let mut achieved_weight = 0.0;
        
        for section in &sections {
            for (section_name, weight) in &self.section_weights {
                if section.name.contains(section_name) {
                    achieved_weight += weight;
                    break;
                }
            }
        }
        
        let structure_score = if total_weight > 0.0 {
            achieved_weight / total_weight * 100.0
        } else {
            0.0
        };
        
        let compliance_rate = if !self.required_sections.is_empty() {
            found_sections.len() as f64 / self.required_sections.len() as f64 * 100.0
        } else {
            0.0
        };
        
        Ok(StructureReport {
            file_path: document_path.to_string_lossy().to_string(),
            total_sections: sections.len(),
            required_sections: found_sections,
            missing_sections,
            optional_sections: self.optional_sections.clone(),
            structure_score,
            compliance_rate,
            success: true,
            error_message: None,
        })
    }
    
    pub fn check_directory(&self, dir_path: &Path) -> Result<Vec<StructureReport>, io::Error> {
        let mut results = Vec::new();
        
        if dir_path.is_dir() {
            for entry in fs::read_dir(dir_path)? {
                let entry = entry?;
                let path = entry.path();
                
                if path.is_file() && path.extension().map_or(false, |ext| ext == "md") {
                    match self.check_document(&path) {
                        Ok(report) => results.push(report),
                        Err(e) => {
                            results.push(StructureReport {
                                file_path: path.to_string_lossy().to_string(),
                                total_sections: 0,
                                required_sections: Vec::new(),
                                missing_sections: Vec::new(),
                                optional_sections: Vec::new(),
                                structure_score: 0.0,
                                compliance_rate: 0.0,
                                success: false,
                                error_message: Some(e.to_string()),
                            });
                        }
                    }
                } else if path.is_dir() {
                    let sub_results = self.check_directory(&path)?;
                    results.extend(sub_results);
                }
            }
        }
        
        Ok(results)
    }
    
    fn extract_sections(&self, content: &str) -> Vec<SectionInfo> {
        let mut sections = Vec::new();
        let lines: Vec<&str> = content.lines().collect();
        
        for (line_num, line) in lines.iter().enumerate() {
            if line.starts_with('#') {
                let level = line.chars().take_while(|&c| c == '#').count();
                let name = line.trim_start_matches('#').trim();
                
                if !name.is_empty() {
                    // 计算该章节的内容长度
                    let mut content_length = 0;
                    let mut in_section = false;
                    
                    for next_line in lines.iter().skip(line_num + 1) {
                        if next_line.starts_with('#') && next_line.chars().take_while(|&c| c == '#').count() <= level {
                            break;
                        }
                        if !next_line.trim().is_empty() {
                            content_length += next_line.len();
                        }
                    }
                    
                    sections.push(SectionInfo {
                        name: name.to_string(),
                        level,
                        line_number: line_num + 1,
                        content_length,
                    });
                }
            }
        }
        
        sections
    }
    
    pub fn generate_report(&self, results: &[StructureReport]) -> String {
        let mut report = String::new();
        
        report.push_str("# 文档结构检查报告\n\n");
        
        // 总体统计
        let total_files = results.len();
        let successful_files = results.iter().filter(|r| r.success).count();
        let avg_structure_score: f64 = results.iter()
            .filter(|r| r.success)
            .map(|r| r.structure_score)
            .sum::<f64>() / successful_files.max(1) as f64;
        
        let avg_compliance_rate: f64 = results.iter()
            .filter(|r| r.success)
            .map(|r| r.compliance_rate)
            .sum::<f64>() / successful_files.max(1) as f64;
        
        report.push_str(&format!("## 总体统计\n"));
        report.push_str(&format!("- **检查文件数**: {}\n", total_files));
        report.push_str(&format!("- **成功文件数**: {}\n", successful_files));
        report.push_str(&format!("- **失败文件数**: {}\n", total_files - successful_files));
        report.push_str(&format!("- **平均结构分数**: {:.2}/100\n", avg_structure_score));
        report.push_str(&format!("- **平均合规率**: {:.2}%\n\n", avg_compliance_rate));
        
        // 按分数分组
        let excellent = results.iter().filter(|r| r.success && r.structure_score >= 90.0).count();
        let good = results.iter().filter(|r| r.success && r.structure_score >= 80.0 && r.structure_score < 90.0).count();
        let fair = results.iter().filter(|r| r.success && r.structure_score >= 70.0 && r.structure_score < 80.0).count();
        let poor = results.iter().filter(|r| r.success && r.structure_score < 70.0).count();
        
        report.push_str(&format!("## 分数分布\n"));
        report.push_str(&format!("- **优秀 (90+)**: {}个 ({:.1}%)\n", excellent, 
            if successful_files > 0 { excellent as f64 / successful_files as f64 * 100.0 } else { 0.0 }));
        report.push_str(&format!("- **良好 (80-89)**: {}个 ({:.1}%)\n", good, 
            if successful_files > 0 { good as f64 / successful_files as f64 * 100.0 } else { 0.0 }));
        report.push_str(&format!("- **一般 (70-79)**: {}个 ({:.1}%)\n", fair, 
            if successful_files > 0 { fair as f64 / successful_files as f64 * 100.0 } else { 0.0 }));
        report.push_str(&format!("- **需要改进 (<70)**: {}个 ({:.1}%)\n\n", poor, 
            if successful_files > 0 { poor as f64 / successful_files as f64 * 100.0 } else { 0.0 }));
        
        // 详细报告
        report.push_str(&format!("## 详细报告\n"));
        for result in results.iter().filter(|r| r.success) {
            report.push_str(&format!("### {}\n", result.file_path));
            report.push_str(&format!("- **结构分数**: {:.2}/100\n", result.structure_score));
            report.push_str(&format!("- **合规率**: {:.2}%\n", result.compliance_rate));
            report.push_str(&format!("- **章节数**: {}\n", result.total_sections));
            
            if !result.missing_sections.is_empty() {
                report.push_str(&format!("- **缺失章节**: {}\n", result.missing_sections.join(", ")));
            }
            
            if !result.required_sections.is_empty() {
                report.push_str(&format!("- **已包含章节**: {}\n", result.required_sections.join(", ")));
            }
            
            report.push_str("\n");
        }
        
        // 失败文件
        let failed_files: Vec<_> = results.iter().filter(|r| !r.success).collect();
        if !failed_files.is_empty() {
            report.push_str("## 失败文件\n\n");
            for result in failed_files {
                report.push_str(&format!("### {}\n", result.file_path));
                report.push_str(&format!("- **错误**: {}\n\n", 
                    result.error_message.as_ref().unwrap_or(&"未知错误".to_string())));
            }
        }
        
        // 必需章节列表
        report.push_str("## 必需章节列表\n\n");
        for section in &self.required_sections {
            report.push_str(&format!("- {}\n", section));
        }
        
        report
    }
}

fn main() -> Result<(), io::Error> {
    let args: Vec<String> = std::env::args().collect();
    
    if args.len() < 2 {
        println!("用法: structure_checker <目录路径>");
        return Ok(());
    }
    
    let dir_path = PathBuf::from(&args[1]);
    
    if !dir_path.exists() {
        eprintln!("错误: 目录不存在: {}", dir_path.display());
        return Ok(());
    }
    
    let checker = StructureChecker::new();
    
    println!("开始文档结构检查...");
    println!("目录: {}", dir_path.display());
    println!();
    
    let results = checker.check_directory(&dir_path)?;
    
    // 生成报告
    let report = checker.generate_report(&results);
    
    // 保存报告
    let report_path = dir_path.join("structure_check_report.md");
    fs::write(&report_path, &report)?;
    
    // 输出摘要
    let total_files = results.len();
    let successful_files = results.iter().filter(|r| r.success).count();
    let avg_structure_score: f64 = results.iter()
        .filter(|r| r.success)
        .map(|r| r.structure_score)
        .sum::<f64>() / successful_files.max(1) as f64;
    
    println!("结构检查完成!");
    println!("检查文件: {}", total_files);
    println!("成功文件: {}", successful_files);
    println!("平均结构分数: {:.2}/100", avg_structure_score);
    println!("报告已保存: {}", report_path.display());
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::tempdir;
    
    #[test]
    fn test_structure_checker() {
        let temp_dir = tempdir().unwrap();
        let test_file = temp_dir.path().join("test.md");
        
        // 创建测试文件
        let test_content = r#"
# 测试文档

## 概述
这是一个测试文档。

## 技术背景
技术背景介绍。

## 核心概念
核心概念说明。

## 技术实现
技术实现细节。

## 应用案例
应用案例展示。

## 性能分析
性能分析结果。

## 最佳实践
最佳实践建议。

## 常见问题
常见问题解答。

## 未来展望
未来发展方向。
"#;
        
        fs::write(&test_file, test_content).unwrap();
        
        // 创建检查器
        let checker = StructureChecker::new();
        
        // 执行检查
        let result = checker.check_document(&test_file).unwrap();
        
        // 验证结果
        assert!(result.success);
        assert!(result.structure_score > 80.0); // 应该有较高的结构分数
        assert!(result.compliance_rate > 80.0); // 应该有较高的合规率
        assert_eq!(result.total_sections, 10); // 应该有10个章节
    }
} 