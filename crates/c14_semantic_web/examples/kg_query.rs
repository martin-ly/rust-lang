use c14_semantic_web::io::load_kg_from_json;
use c14_semantic_web::reasoning::{common_prerequisites, must_learn_before, reason};
use std::env;

fn main() {
    let path = env::args()
        .nth(1)
        .unwrap_or_else(|| "concept/00_meta/kg_data_v2.json".to_string());

    let kg = load_kg_from_json(&path).expect("加载失败");
    let result = reason(&kg);

    println!("=== 学习路径推理 ===\n");

    // 打印每个概念的前置概念
    for (concept, deps) in &result.prerequisites {
        let entity = kg.get_entity(concept).unwrap();
        let label = entity.label_for("zh").unwrap_or(concept);
        if !deps.is_empty() {
            let dep_labels: Vec<_> = deps
                .iter()
                .map(|d| kg.get_entity(d).and_then(|e| e.label_for("zh")).unwrap_or(d.as_str()))
                .collect();
            println!("学习「{}」之前需掌握: {}", label, dep_labels.join(", "));
        }
    }

    println!("\n=== 循环依赖检测 ===");
    if result.cycles.is_empty() {
        println!("未发现 dependsOn 循环依赖");
    } else {
        for cycle in &result.cycles {
            println!("发现循环: {:?}", cycle);
        }
    }

    println!("\n=== 示例查询 ===");
    println!(
        "学习 Lifetimes 之前必须学习 Ownership? {}",
        must_learn_before(&kg, "ex:Lifetimes", "ex:Ownership")
    );

    let common = common_prerequisites(&kg, "ex:Lifetimes", "ex:AsyncAwait");
    let common_labels: Vec<_> = common
        .iter()
        .map(|d| kg.get_entity(d).and_then(|e| e.label_for("zh")).unwrap_or(d.as_str()))
        .collect();
    println!("Lifetimes 与 AsyncAwait 的共同前置概念: {}", common_labels.join(", "));
}
