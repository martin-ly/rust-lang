use c14_semantic_web::graph::{
    Entity, EntityType, KnowledgeGraph, LangString, Relation, RelationMeta,
};
use c14_semantic_web::reasoning::reason;
use c14_semantic_web::validation::Validator;

fn build_test_kg() -> KnowledgeGraph {
    let mut kg = KnowledgeGraph::new();

    let make_entity = |id: &str, ty: EntityType, label: &str| Entity {
        id: id.into(),
        ty,
        pref_label: vec![
            LangString {
                value: label.into(),
                language: "en".into(),
            },
            LangString {
                value: label.into(),
                language: "zh".into(),
            },
        ],
        alt_label: vec![],
        definition: vec![],
        scope_note: vec![],
        path: None,
        layer: Some("L1".into()),
        bloom: Some("Understand".into()),
        asp: Some("S".into()),
    };

    kg.add_entity(make_entity(
        "ex:Ownership",
        EntityType::Concept,
        "Ownership",
    ));
    kg.add_entity(make_entity(
        "ex:Borrowing",
        EntityType::Concept,
        "Borrowing",
    ));
    kg.add_entity(make_entity(
        "ex:Lifetimes",
        EntityType::Concept,
        "Lifetimes",
    ));

    kg.add_relation(Relation {
        subject: "ex:Borrowing".into(),
        predicate: "ex:dependsOn".into(),
        object: "ex:Ownership".into(),
        meta: RelationMeta {
            source: "test".into(),
            confidence: Some(1.0),
            version: Some("1.97.0".into()),
            reviewed: Some(true),
        },
    });

    kg.add_relation(Relation {
        subject: "ex:Lifetimes".into(),
        predicate: "ex:dependsOn".into(),
        object: "ex:Borrowing".into(),
        meta: RelationMeta {
            source: "test".into(),
            confidence: Some(1.0),
            version: Some("1.97.0".into()),
            reviewed: Some(true),
        },
    });

    kg
}

#[test]
fn test_validation_passes() {
    let kg = build_test_kg();
    let report = Validator::new().validate(&kg);
    assert!(report.is_valid(), "{:?}", report.issues);
}

#[test]
fn test_transitive_closure() {
    let kg = build_test_kg();
    let result = reason(&kg);

    let lifetime_deps = result.transitive_closure.get("ex:Lifetimes").unwrap();
    assert!(lifetime_deps.contains("ex:Ownership"));
    assert!(lifetime_deps.contains("ex:Borrowing"));
    assert!(!lifetime_deps.contains("ex:Lifetimes")); // 不应包含自身
}

#[test]
fn test_cycle_detection() {
    let mut kg = build_test_kg();
    kg.add_relation(Relation {
        subject: "ex:Ownership".into(),
        predicate: "ex:dependsOn".into(),
        object: "ex:Lifetimes".into(),
        meta: RelationMeta {
            source: "test".into(),
            confidence: Some(0.5),
            version: Some("1.97.0".into()),
            reviewed: Some(false),
        },
    });

    let result = reason(&kg);
    assert!(!result.cycles.is_empty());
}
