// AI and Machine Learning with Rust
// 人工智能与机器学习

pub mod neural_networks;
pub mod machine_learning;
pub mod deep_learning;
pub mod nlp;
pub mod computer_vision;

/// AI模块的主要功能
pub struct AIModule {
    pub name: String,
    pub version: String,
}

impl AIModule {
    pub fn new(name: String) -> Self {
        Self {
            name,
            version: "0.1.0".to_string(),
        }
    }
    
    pub fn get_info(&self) -> String {
        format!("AI模块: {} v{}", self.name, self.version)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_ai_module() {
        let ai = AIModule::new("测试模块".to_string());
        assert_eq!(ai.get_info(), "AI模块: 测试模块 v0.1.0");
    }
}
