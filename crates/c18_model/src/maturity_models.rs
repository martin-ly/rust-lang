//! 成熟度模型实现
//! 
//! 本模块实现了各种软件工程成熟度模型，
//! 包括 CMMI-DEV、P3M3、MICOSE4aPS、AssessITS 等模型。

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use thiserror::Error;

/// 成熟度模型错误类型
#[derive(Error, Debug)]
pub enum MaturityModelError {
    #[error("模型不存在: {0}")]
    ModelNotFound(String),
    
    #[error("评估失败: {0}")]
    AssessmentFailed(String),
    
    #[error("级别无效: {0}")]
    InvalidLevel(String),
}

/// 成熟度模型类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum MaturityModel {
    // 软件开发成熟度
    CMMIDev,     // CMMI-DEV v2.0 能力成熟度模型集成
    TMMi,        // TMMi 测试成熟度模型集成
    SAMM,        // SAMM 软件保障成熟度模型
    
    // 项目管理成熟度
    P3M3,        // P3M3 项目组合、项目群和项目管理成熟度模型
    OPM3,        // OPM3 组织项目管理成熟度模型
    PRINCE2,     // PRINCE2 项目管理方法论
    
    // 安全成熟度
    BSIMM,       // BSIMM 软件安全构建成熟度模型
    OpenSAMM,    // OpenSAMM 软件保障成熟度模型
    NISTCSF,     // NIST CSF 网络安全框架成熟度
    
    // 敏捷成熟度
    AgileMaturity, // Agile Maturity Model 敏捷成熟度模型
    ScrumMaturity, // Scrum Maturity Model Scrum成熟度模型
    DevOpsMaturity, // DevOps Maturity Model DevOps成熟度模型
    
    // 工业软件成熟度
    MICOSE4aPS,  // MICOSE4aPS 工业控制软件成熟度模型
    AssessITS,   // AssessITS IT和网络安全风险评估方法
}

/// 成熟度级别
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, PartialOrd)]
pub enum MaturityLevel {
    Level0, // 初始级
    Level1, // 已管理级
    Level2, // 已定义级
    Level3, // 已量化管理级
    Level4, // 优化级
    Level5, // 创新级
}

/// 过程域
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessArea {
    pub id: String,
    pub name: String,
    pub description: String,
    pub category: ProcessCategory,
    pub practices: Vec<Practice>,
}

/// 过程类别
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ProcessCategory {
    ProcessManagement,
    ProjectManagement,
    Engineering,
    Support,
}

/// 实践
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Practice {
    pub id: String,
    pub name: String,
    pub description: String,
    pub level: MaturityLevel,
    pub evidence_required: Vec<String>,
}

/// 评估结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AssessmentResult {
    pub model: MaturityModel,
    pub overall_level: MaturityLevel,
    pub process_areas: HashMap<String, ProcessAreaAssessment>,
    pub score: f64,
    pub recommendations: Vec<String>,
    pub next_steps: Vec<String>,
}

/// 过程域评估
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessAreaAssessment {
    pub process_area: ProcessArea,
    pub current_level: MaturityLevel,
    pub target_level: MaturityLevel,
    pub score: f64,
    pub gaps: Vec<String>,
    pub strengths: Vec<String>,
}

/// 成熟度评估器
pub struct MaturityAssessor {
    models: HashMap<MaturityModel, Vec<ProcessArea>>,
}

impl MaturityAssessor {
    /// 创建新的成熟度评估器
    pub fn new() -> Self {
        let mut models = HashMap::new();
        
        // 初始化 CMMI-DEV 模型
        models.insert(MaturityModel::CMMIDev, Self::cmmi_dev_process_areas());
        
        // 初始化 P3M3 模型
        models.insert(MaturityModel::P3M3, Self::p3m3_process_areas());
        
        // 初始化 MICOSE4aPS 模型
        models.insert(MaturityModel::MICOSE4aPS, Self::micose4aps_process_areas());
        
        // 初始化 AssessITS 模型
        models.insert(MaturityModel::AssessITS, Self::assessits_process_areas());
        
        // 2025年新增成熟度模型 - 暂时注释，待实现
        // models.insert(MaturityModel::TMMi, Self::tmmi_process_areas());
        // models.insert(MaturityModel::SAMM, Self::samm_process_areas());
        // models.insert(MaturityModel::BSIMM, Self::bsimm_process_areas());
        // models.insert(MaturityModel::AgileMaturity, Self::agile_maturity_process_areas());
        // models.insert(MaturityModel::DevOpsMaturity, Self::devops_maturity_process_areas());
        // models.insert(MaturityModel::OPM3, Self::opm3_process_areas());
        // models.insert(MaturityModel::PRINCE2, Self::prince2_process_areas());
        // models.insert(MaturityModel::OpenSAMM, Self::opensamm_process_areas());
        // models.insert(MaturityModel::NISTCSF, Self::nist_csf_process_areas());
        // models.insert(MaturityModel::ScrumMaturity, Self::scrum_maturity_process_areas());

        Self { models }
    }

    /// 评估成熟度
    pub fn assess_maturity(
        &self,
        model: MaturityModel,
        evidence: &HashMap<String, Vec<String>>,
    ) -> Result<AssessmentResult, MaturityModelError> {
        let process_areas = self.models.get(&model)
            .ok_or_else(|| MaturityModelError::ModelNotFound(format!("{:?}", model)))?;

        let mut process_area_assessments = HashMap::new();
        let mut total_score = 0.0;
        let mut total_weight = 0.0;

        for process_area in process_areas {
            let assessment = self.assess_process_area(process_area, evidence)?;
            let weight = self.get_process_area_weight(process_area);
            
            total_score += assessment.score * weight;
            total_weight += weight;
            
            process_area_assessments.insert(process_area.id.clone(), assessment);
        }

        let overall_score = if total_weight > 0.0 { total_score / total_weight } else { 0.0 };
        let overall_level = self.score_to_level(overall_score);
        
        let recommendations = self.generate_recommendations(&process_area_assessments);
        let next_steps = self.generate_next_steps(&process_area_assessments, overall_level);

        Ok(AssessmentResult {
            model,
            overall_level,
            process_areas: process_area_assessments,
            score: overall_score,
            recommendations,
            next_steps,
        })
    }

    /// 评估过程域
    fn assess_process_area(
        &self,
        process_area: &ProcessArea,
        evidence: &HashMap<String, Vec<String>>,
    ) -> Result<ProcessAreaAssessment, MaturityModelError> {
        let mut current_level = MaturityLevel::Level0;
        let mut gaps = Vec::new();
        let mut strengths = Vec::new();

        // 检查每个级别的实践
        for level in [MaturityLevel::Level1, MaturityLevel::Level2, MaturityLevel::Level3, MaturityLevel::Level4, MaturityLevel::Level5] {
            let level_practices: Vec<_> = process_area.practices.iter()
                .filter(|p| p.level == level)
                .collect();

            let mut level_score = 0.0;
            for practice in &level_practices {
                if let Some(evidence_list) = evidence.get(&practice.id) {
                    let practice_score = self.evaluate_practice(practice, evidence_list);
                    level_score += practice_score;
                    
                    if practice_score >= 0.8 {
                        strengths.push(format!("{}: {}", practice.name, "优秀"));
                    } else if practice_score < 0.5 {
                        gaps.push(format!("{}: {}", practice.name, "需要改进"));
                    }
                } else {
                    gaps.push(format!("{}: {}", practice.name, "缺少证据"));
                }
            }

            if !level_practices.is_empty() {
                let level_average = level_score / level_practices.len() as f64;
                if level_average >= 0.8 {
                    current_level = level;
                } else {
                    break;
                }
            }
        }

        let target_level = MaturityLevel::Level3; // 默认目标级别
        let score = self.level_to_score(&current_level);

        Ok(ProcessAreaAssessment {
            process_area: process_area.clone(),
            current_level,
            target_level,
            score,
            gaps,
            strengths,
        })
    }

    /// 评估实践
    fn evaluate_practice(&self, practice: &Practice, evidence: &[String]) -> f64 {
        let required_evidence = practice.evidence_required.len();
        if required_evidence == 0 {
            return 1.0;
        }

        let provided_evidence = evidence.len();
        (provided_evidence as f64 / required_evidence as f64).min(1.0)
    }

    /// 获取过程域权重
    fn get_process_area_weight(&self, _process_area: &ProcessArea) -> f64 {
        1.0 // 简化实现，所有过程域权重相等
    }

    /// 分数转换为级别
    fn score_to_level(&self, score: f64) -> MaturityLevel {
        match score {
            s if s >= 0.9 => MaturityLevel::Level5,
            s if s >= 0.8 => MaturityLevel::Level4,
            s if s >= 0.7 => MaturityLevel::Level3,
            s if s >= 0.6 => MaturityLevel::Level2,
            s if s >= 0.5 => MaturityLevel::Level1,
            _ => MaturityLevel::Level0,
        }
    }

    /// 级别转换为分数
    fn level_to_score(&self, level: &MaturityLevel) -> f64 {
        match level {
            MaturityLevel::Level0 => 0.0,
            MaturityLevel::Level1 => 0.2,
            MaturityLevel::Level2 => 0.4,
            MaturityLevel::Level3 => 0.6,
            MaturityLevel::Level4 => 0.8,
            MaturityLevel::Level5 => 1.0,
        }
    }

    /// 生成建议
    fn generate_recommendations(&self, assessments: &HashMap<String, ProcessAreaAssessment>) -> Vec<String> {
        let mut recommendations = Vec::new();

        for assessment in assessments.values() {
            if assessment.score < 0.6 {
                recommendations.push(format!(
                    "改进 {} 过程域，当前级别: {:?}",
                    assessment.process_area.name,
                    assessment.current_level
                ));
            }
        }

        if recommendations.is_empty() {
            recommendations.push("所有过程域表现良好，建议继续优化".to_string());
        }

        recommendations
    }

    /// 生成下一步行动
    fn generate_next_steps(&self, _assessments: &HashMap<String, ProcessAreaAssessment>, overall_level: MaturityLevel) -> Vec<String> {
        let mut next_steps = Vec::new();

        match overall_level {
            MaturityLevel::Level0 => {
                next_steps.push("建立基础过程管理".to_string());
                next_steps.push("制定过程文档".to_string());
            },
            MaturityLevel::Level1 => {
                next_steps.push("标准化过程".to_string());
                next_steps.push("建立过程度量".to_string());
            },
            MaturityLevel::Level2 => {
                next_steps.push("量化过程管理".to_string());
                next_steps.push("建立过程数据库".to_string());
            },
            MaturityLevel::Level3 => {
                next_steps.push("持续过程改进".to_string());
                next_steps.push("创新过程实践".to_string());
            },
            MaturityLevel::Level4 => {
                next_steps.push("优化过程性能".to_string());
                next_steps.push("推广最佳实践".to_string());
            },
            MaturityLevel::Level5 => {
                next_steps.push("保持卓越水平".to_string());
                next_steps.push("探索新技术".to_string());
            },
        }

        next_steps
    }

    /// CMMI-DEV 过程域
    fn cmmi_dev_process_areas() -> Vec<ProcessArea> {
        vec![
            ProcessArea {
                id: "project_planning".to_string(),
                name: "项目计划".to_string(),
                description: "建立和维护项目计划".to_string(),
                category: ProcessCategory::ProjectManagement,
                practices: vec![
                    Practice {
                        id: "pp_1_1".to_string(),
                        name: "建立项目计划".to_string(),
                        description: "建立和维护项目计划".to_string(),
                        level: MaturityLevel::Level2,
                        evidence_required: vec!["项目计划文档".to_string(), "进度跟踪记录".to_string()],
                    },
                ],
            },
            ProcessArea {
                id: "requirements_management".to_string(),
                name: "需求管理".to_string(),
                description: "管理项目需求".to_string(),
                category: ProcessCategory::Engineering,
                practices: vec![
                    Practice {
                        id: "req_1_1".to_string(),
                        name: "获取需求".to_string(),
                        description: "获取并理解需求".to_string(),
                        level: MaturityLevel::Level2,
                        evidence_required: vec!["需求文档".to_string(), "需求评审记录".to_string()],
                    },
                ],
            },
        ]
    }

    /// P3M3 过程域
    fn p3m3_process_areas() -> Vec<ProcessArea> {
        vec![
            ProcessArea {
                id: "portfolio_management".to_string(),
                name: "项目组合管理".to_string(),
                description: "管理项目组合".to_string(),
                category: ProcessCategory::ProcessManagement,
                practices: vec![
                    Practice {
                        id: "pfm_1_1".to_string(),
                        name: "项目组合规划".to_string(),
                        description: "规划项目组合".to_string(),
                        level: MaturityLevel::Level2,
                        evidence_required: vec!["组合规划文档".to_string()],
                    },
                ],
            },
        ]
    }

    /// MICOSE4aPS 过程域
    fn micose4aps_process_areas() -> Vec<ProcessArea> {
        vec![
            ProcessArea {
                id: "software_reuse".to_string(),
                name: "软件重用".to_string(),
                description: "软件重用评估".to_string(),
                category: ProcessCategory::Engineering,
                practices: vec![
                    Practice {
                        id: "sru_1_1".to_string(),
                        name: "重用评估".to_string(),
                        description: "评估软件重用能力".to_string(),
                        level: MaturityLevel::Level2,
                        evidence_required: vec!["重用评估报告".to_string()],
                    },
                ],
            },
        ]
    }

    /// AssessITS 过程域
    fn assessits_process_areas() -> Vec<ProcessArea> {
        vec![
            ProcessArea {
                id: "risk_assessment".to_string(),
                name: "风险评估".to_string(),
                description: "IT和网络安全风险评估".to_string(),
                category: ProcessCategory::Support,
                practices: vec![
                    Practice {
                        id: "ra_1_1".to_string(),
                        name: "风险识别".to_string(),
                        description: "识别IT和网络安全风险".to_string(),
                        level: MaturityLevel::Level2,
                        evidence_required: vec!["风险清单".to_string(), "风险评估报告".to_string()],
                    },
                ],
            },
        ]
    }
}

impl Default for MaturityAssessor {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_maturity_assessor_creation() {
        let assessor = MaturityAssessor::new();
        assert_eq!(assessor.models.len(), 4);
    }

    #[test]
    fn test_cmmi_assessment() {
        let assessor = MaturityAssessor::new();
        let mut evidence = HashMap::new();
        evidence.insert("pp_1_1".to_string(), vec!["项目计划文档".to_string()]);
        
        let result = assessor.assess_maturity(MaturityModel::CMMIDev, &evidence);
        assert!(result.is_ok());
        
        let assessment = result.unwrap();
        assert_eq!(assessment.model, MaturityModel::CMMIDev);
    }

    #[test]
    fn test_score_to_level() {
        let assessor = MaturityAssessor::new();
        
        assert_eq!(assessor.score_to_level(0.95), MaturityLevel::Level5);
        assert_eq!(assessor.score_to_level(0.85), MaturityLevel::Level4);
        assert_eq!(assessor.score_to_level(0.75), MaturityLevel::Level3);
        assert_eq!(assessor.score_to_level(0.65), MaturityLevel::Level2);
        assert_eq!(assessor.score_to_level(0.55), MaturityLevel::Level1);
        assert_eq!(assessor.score_to_level(0.45), MaturityLevel::Level0);
    }
}
