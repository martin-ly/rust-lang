use c09_design_pattern::{get_patterns_by_execution_model, ExecutionModel};

#[test]
fn execution_model_sync_has_items() {
    let sync_patterns = get_patterns_by_execution_model(ExecutionModel::Sync);
    assert!(!sync_patterns.is_empty(), "Sync patterns should not be empty");
}

#[test]
fn execution_model_async_has_items() {
    let async_patterns = get_patterns_by_execution_model(ExecutionModel::Async);
    assert!(!async_patterns.is_empty(), "Async patterns should not be empty");
}

#[test]
fn execution_model_hybrid_has_items() {
    let hybrid_patterns = get_patterns_by_execution_model(ExecutionModel::Hybrid);
    assert!(!hybrid_patterns.is_empty(), "Hybrid patterns should not be empty");
}

