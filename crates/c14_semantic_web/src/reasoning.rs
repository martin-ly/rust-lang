use crate::graph::KnowledgeGraph;
use std::collections::{HashMap, HashSet};

/// 推理结果。
#[derive(Debug, Clone)]
pub struct ReasoningResult {
    pub transitive_closure: HashMap<String, HashSet<String>>,
    pub cycles: Vec<Vec<String>>,
    pub prerequisites: HashMap<String, HashSet<String>>,
    pub follow_ups: HashMap<String, HashSet<String>>,
}

/// 对知识图谱执行基础推理。
pub fn reason(kg: &KnowledgeGraph) -> ReasoningResult {
    let closure = kg.transitive_closure("ex:dependsOn");
    let cycles = kg.detect_cycles("ex:dependsOn");

    let mut prerequisites: HashMap<String, HashSet<String>> = HashMap::new();
    let mut follow_ups: HashMap<String, HashSet<String>> = HashMap::new();

    for (node, deps) in &closure {
        // 前置概念：所有传递依赖
        prerequisites.insert(node.clone(), deps.clone());

        // 后置概念：哪些节点依赖当前节点
        for (other, other_deps) in &closure {
            if other != node && other_deps.contains(node) {
                follow_ups.entry(node.clone()).or_default().insert(other.clone());
            }
        }
    }

    ReasoningResult {
        transitive_closure: closure,
        cycles,
        prerequisites,
        follow_ups,
    }
}

/// 判断学习概念 A 之前是否必须先学习概念 B。
pub fn must_learn_before(kg: &KnowledgeGraph, target: &str, prerequisite: &str) -> bool {
    let closure = kg.transitive_closure("ex:dependsOn");
    closure
        .get(target)
        .map(|deps| deps.contains(prerequisite))
        .unwrap_or(false)
}

/// 找出所有共同前置概念。
pub fn common_prerequisites(kg: &KnowledgeGraph, a: &str, b: &str) -> HashSet<String> {
    let closure = kg.transitive_closure("ex:dependsOn");
    let a_deps = closure.get(a).cloned().unwrap_or_default();
    let b_deps = closure.get(b).cloned().unwrap_or_default();
    a_deps.intersection(&b_deps).cloned().collect()
}
