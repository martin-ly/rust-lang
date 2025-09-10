//! c18_model - 模型系统分析
//! 
//! 本库提供了软件架构、设计模式、形式化方法、领域特定语言、
//! AI/ML集成和跨语言互操作性等功能的实现。

pub mod architecture;
pub mod patterns;
pub mod formal_methods;
pub mod domain_specific_languages;
pub mod ai_ml_integration;
pub mod cross_language_interoperability;

// 重新导出主要类型和trait
pub use architecture::{
    ArchitectureDescription, ArchitectureViewpoint, ArchitectureView, ArchitectureModel,
    ArchitectureElement, ArchitectureRelationship, Concern, Stakeholder, ElementType,
    RelationshipType, ConcernCategory, Interface, InterfaceType, Operation, Parameter,
    ParameterDirection, ModelKind, QualityScore, QualityAttributeEvaluator,
    ArchitectureDescriptionBuilder, StandardViewpoints, QualityAttributes,
    microservice_example,
};

pub use patterns::{
    singleton, builder, factory, observer, strategy, producer_consumer,
    functional, error_handling,
};

pub use formal_methods::{
    formal_languages, verification, transformation, implementations, tools,
};

pub use domain_specific_languages::{
    embedded_dsl, query_builder, state_machine_dsl, config_dsl, dsl_toolkit,
};

pub use ai_ml_integration::{
    type_safe_ml, nlp, blockchain, quantum_computing, ai_ml_toolkit,
};

pub use cross_language_interoperability::{
    ffi_safety, type_conversion, memory_management, interoperability_toolkit,
};

/// 模型系统分析的主要入口点
pub struct ModelSystemAnalyzer {
    pub architecture: architecture::ArchitectureDescription,
    pub formal_methods: formal_methods::tools::FormalMethodsToolkit,
    pub dsl: domain_specific_languages::dsl_toolkit::DSLToolkit,
    pub ai_ml: ai_ml_integration::ai_ml_toolkit::AIMLToolkit,
    pub interoperability: cross_language_interoperability::interoperability_toolkit::InteroperabilityToolkit,
}

impl ModelSystemAnalyzer {
    /// 创建新的模型系统分析器
    pub fn new() -> Self {
        Self {
            architecture: architecture::ArchitectureDescription {
                id: "default_arch".to_string(),
                name: "Default Architecture".to_string(),
                version: "1.0.0".to_string(),
                viewpoints: Vec::new(),
                views: Vec::new(),
                models: Vec::new(),
                concerns: Vec::new(),
                stakeholders: Vec::new(),
            },
            formal_methods: formal_methods::tools::FormalMethodsToolkit::new(),
            dsl: domain_specific_languages::dsl_toolkit::DSLToolkit::new(),
            ai_ml: ai_ml_integration::ai_ml_toolkit::AIMLToolkit::new(),
            interoperability: cross_language_interoperability::interoperability_toolkit::InteroperabilityToolkit::new(),
        }
    }

    /// 分析软件架构
    pub fn analyze_architecture(&self) -> &architecture::ArchitectureDescription {
        &self.architecture
    }


    /// 分析形式化方法
    pub fn analyze_formal_methods(&self) -> &formal_methods::tools::FormalMethodsToolkit {
        &self.formal_methods
    }

    /// 分析领域特定语言
    pub fn analyze_dsl(&self) -> &domain_specific_languages::dsl_toolkit::DSLToolkit {
        &self.dsl
    }

    /// 分析AI/ML集成
    pub fn analyze_ai_ml(&self) -> &ai_ml_integration::ai_ml_toolkit::AIMLToolkit {
        &self.ai_ml
    }

    /// 分析跨语言互操作性
    pub fn analyze_interoperability(&self) -> &cross_language_interoperability::interoperability_toolkit::InteroperabilityToolkit {
        &self.interoperability
    }
}

impl Default for ModelSystemAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_model_system_analyzer_creation() {
        let analyzer = ModelSystemAnalyzer::new();
        assert_eq!(analyzer.architecture.name, "Default Architecture");
    }

    #[test]
    fn test_model_system_analyzer_default() {
        let analyzer = ModelSystemAnalyzer::default();
        assert_eq!(analyzer.architecture.name, "Default Architecture");
    }

    #[test]
    fn test_architecture_analysis() {
        let analyzer = ModelSystemAnalyzer::new();
        let architecture = analyzer.analyze_architecture();
        assert_eq!(architecture.name, "Default Architecture");
    }


    #[test]
    fn test_formal_methods_analysis() {
        let analyzer = ModelSystemAnalyzer::new();
        let formal_methods = analyzer.analyze_formal_methods();
        assert!(formal_methods.verify_algebraic_property("associativity"));
    }

    #[test]
    fn test_dsl_analysis() {
        let analyzer = ModelSystemAnalyzer::new();
        let dsl = analyzer.analyze_dsl();
        let expression = dsl.create_complex_expression();
        assert_eq!(expression.evaluate(), 16.0);
    }

    #[test]
    fn test_ai_ml_analysis() {
        let analyzer = ModelSystemAnalyzer::new();
        let ai_ml = analyzer.analyze_ai_ml();
        let ml_result = ai_ml.run_ml_prediction(&[1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0]);
        assert_eq!(ml_result.len(), 1);
    }

    #[test]
    fn test_interoperability_analysis() {
        let mut analyzer = ModelSystemAnalyzer::new();
        let interoperability = &mut analyzer.interoperability;
        let address = interoperability.safe_allocate(1024).unwrap();
        assert!(interoperability.safe_deallocate(address).is_ok());
    }
}
