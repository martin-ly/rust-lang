// 搜索结果导出模块

use crate::{SearchResult, config::ExportFormat};
use std::fs::File;
use std::io::Write;
use std::path::Path;

/// 导出搜索结果
pub fn export_results<P: AsRef<Path>>(
    results: &[SearchResult],
    path: P,
    format: &ExportFormat,
) -> Result<(), Box<dyn std::error::Error>> {
    match format {
        ExportFormat::Json => export_json(results, path),
        ExportFormat::Csv => export_csv(results, path),
        ExportFormat::Markdown => export_markdown(results, path),
    }
}

/// 导出为 JSON
fn export_json<P: AsRef<Path>>(
    results: &[SearchResult],
    path: P,
) -> Result<(), Box<dyn std::error::Error>> {
    let json = serde_json::to_string_pretty(results)?;
    let mut file = File::create(path)?;
    file.write_all(json.as_bytes())?;
    Ok(())
}

/// 导出为 CSV
fn export_csv<P: AsRef<Path>>(
    results: &[SearchResult],
    path: P,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut wtr = csv::Writer::from_path(path)?;
    
    // 写入表头
    wtr.write_record(&[
        "Rank",
        "File Path",
        "Line Number",
        "Module",
        "Doc Type",
        "Relevance Score",
        "Context",
    ])?;
    
    // 写入数据
    for (i, result) in results.iter().enumerate() {
        wtr.write_record(&[
            (i + 1).to_string(),
            result.file_path.clone(),
            result.line_number.to_string(),
            result.module.clone(),
            format!("{:?}", result.doc_type),
            result.relevance_score.to_string(),
            result.context.replace('\n', " "),
        ])?;
    }
    
    wtr.flush()?;
    Ok(())
}

/// 导出为 Markdown
fn export_markdown<P: AsRef<Path>>(
    results: &[SearchResult],
    path: P,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut file = File::create(path)?;
    
    // 写入标题
    writeln!(file, "# 搜索结果\n")?;
    writeln!(file, "**总结果数**: {}\n", results.len())?;
    writeln!(file, "---\n")?;
    
    // 写入每个结果
    for (i, result) in results.iter().enumerate() {
        writeln!(file, "## {}. {}\n", i + 1, result.file_path)?;
        writeln!(file, "- **行号**: {}", result.line_number)?;
        writeln!(file, "- **模块**: {}", result.module)?;
        writeln!(file, "- **类型**: {:?}", result.doc_type)?;
        writeln!(file, "- **相关性分数**: {:.2}", result.relevance_score)?;
        writeln!(file, "\n**匹配内容**:\n")?;
        writeln!(file, "```")?;
        writeln!(file, "{}", result.context)?;
        writeln!(file, "```\n")?;
        writeln!(file, "---\n")?;
    }
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::DocumentType;
    
    #[test]
    fn test_export_json() {
        let results = vec![
            SearchResult {
                file_path: "test.md".to_string(),
                line_number: 10,
                context: "Test context".to_string(),
                relevance_score: 5.0,
                doc_type: DocumentType::MainDoc,
                module: "test".to_string(),
            },
        ];
        
        let temp_file = std::env::temp_dir().join("test_export.json");
        export_json(&results, &temp_file).unwrap();
        assert!(temp_file.exists());
        std::fs::remove_file(temp_file).ok();
    }
}

