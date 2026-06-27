use c14_semantic_web::io::load_kg_from_json;
use c14_semantic_web::validation::Validator;
use std::env;

fn main() {
    let path = env::args()
        .nth(1)
        .unwrap_or_else(|| "concept/00_meta/kg_data_v2.json".to_string());

    println!("加载知识图谱: {}", path);
    let kg = load_kg_from_json(&path).expect("加载失败");

    println!("实体数量: {}", kg.entities().len());
    println!("关系数量: {}", kg.relations().len());

    let report = Validator::new().validate(&kg);

    println!(
        "\n验证结果: {}",
        if report.is_valid() {
            "✅ 通过"
        } else {
            "❌ 失败"
        }
    );

    if !report.errors().is_empty() {
        println!("\n错误:");
        for issue in report.errors() {
            println!("  [{}] {}", issue.target, issue.message);
        }
    }

    if !report.warnings().is_empty() {
        println!("\n警告:");
        for issue in report.warnings() {
            println!("  [{}] {}", issue.target, issue.message);
        }
    }
}
