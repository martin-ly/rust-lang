//! # 大学课程对标 / University Course Benchmarking
//!
//! 本模块对标著名大学的工作流相关课程，包括 MIT、Stanford 等，
//! 确保我们的实现符合学术标准和最佳实践。
//!
//! This module benchmarks against renowned university courses related to workflows,
//! including MIT, Stanford, etc., to ensure our implementation follows academic standards and best practices.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 大学课程基准测试 / University Course Benchmark
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UniversityCourseBenchmark {
    pub university: String,
    pub course_name: String,
    pub course_code: String,
    pub curriculum: CourseCurriculum,
    pub learning_outcomes: Vec<LearningOutcome>,
    pub assessment_criteria: Vec<AssessmentCriteria>,
}

/// 课程大纲 / Course Curriculum
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CourseCurriculum {
    pub modules: Vec<CourseModule>,
    pub prerequisites: Vec<String>,
    pub total_hours: u32,
    pub credits: u8,
}

/// 课程模块 / Course Module
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CourseModule {
    pub id: String,
    pub title: String,
    pub description: String,
    pub topics: Vec<String>,
    pub duration_hours: u32,
    pub difficulty_level: DifficultyLevel,
}

/// 难度级别 / Difficulty Level
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum DifficultyLevel {
    Beginner,
    Intermediate,
    Advanced,
    Expert,
}

/// 学习成果 / Learning Outcome
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LearningOutcome {
    pub id: String,
    pub description: String,
    pub category: LearningCategory,
    pub assessment_method: String,
}

/// 学习类别 / Learning Category
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum LearningCategory {
    Knowledge,
    Comprehension,
    Application,
    Analysis,
    Synthesis,
    Evaluation,
}

/// 评估标准 / Assessment Criteria
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AssessmentCriteria {
    pub id: String,
    pub description: String,
    pub weight: f64,
    pub rubric: AssessmentRubric,
}

/// 评估量表 / Assessment Rubric
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AssessmentRubric {
    pub excellent: String,
    pub good: String,
    pub satisfactory: String,
    pub needs_improvement: String,
}

/// MIT 工作流课程 / MIT Workflow Course
pub struct MITWorkflowCourse {
    benchmark: UniversityCourseBenchmark,
}

impl Default for MITWorkflowCourse {
    fn default() -> Self {
        Self::new()
    }
}

impl MITWorkflowCourse {
    /// 创建 MIT 工作流课程基准测试 / Create MIT workflow course benchmark
    pub fn new() -> Self {
        Self {
            benchmark: UniversityCourseBenchmark {
                university: "Massachusetts Institute of Technology".to_string(),
                course_name: "Advanced Workflow Systems and Process Algebra".to_string(),
                course_code: "6.824".to_string(),
                curriculum: Self::mit_curriculum(),
                learning_outcomes: Self::mit_learning_outcomes(),
                assessment_criteria: Self::mit_assessment_criteria(),
            },
        }
    }

    /// MIT 课程大纲 / MIT curriculum
    fn mit_curriculum() -> CourseCurriculum {
        CourseCurriculum {
            modules: vec![
                CourseModule {
                    id: "MOD_001".to_string(),
                    title: "Process Algebra Foundations".to_string(),
                    description: "进程代数理论基础，包括 CCS、CSP、π-演算等".to_string(),
                    topics: vec![
                        "CCS (Calculus of Communicating Systems)".to_string(),
                        "CSP (Communicating Sequential Processes)".to_string(),
                        "π-calculus".to_string(),
                        "Bisimulation and Equivalence".to_string(),
                    ],
                    duration_hours: 20,
                    difficulty_level: DifficultyLevel::Advanced,
                },
                CourseModule {
                    id: "MOD_002".to_string(),
                    title: "Distributed Workflow Systems".to_string(),
                    description: "分布式工作流系统的设计和实现".to_string(),
                    topics: vec![
                        "Distributed State Management".to_string(),
                        "Consensus Algorithms".to_string(),
                        "Fault Tolerance".to_string(),
                        "Event Sourcing".to_string(),
                    ],
                    duration_hours: 25,
                    difficulty_level: DifficultyLevel::Expert,
                },
                CourseModule {
                    id: "MOD_003".to_string(),
                    title: "Formal Verification of Workflows".to_string(),
                    description: "工作流的形式化验证方法".to_string(),
                    topics: vec![
                        "Model Checking".to_string(),
                        "Temporal Logic".to_string(),
                        "Property Specification".to_string(),
                        "Verification Tools".to_string(),
                    ],
                    duration_hours: 18,
                    difficulty_level: DifficultyLevel::Expert,
                },
                CourseModule {
                    id: "MOD_004".to_string(),
                    title: "Performance Analysis and Optimization".to_string(),
                    description: "工作流系统的性能分析和优化".to_string(),
                    topics: vec![
                        "Performance Modeling".to_string(),
                        "Bottleneck Analysis".to_string(),
                        "Optimization Techniques".to_string(),
                        "Benchmarking".to_string(),
                    ],
                    duration_hours: 15,
                    difficulty_level: DifficultyLevel::Advanced,
                },
            ],
            prerequisites: vec![
                "6.033 Computer Systems Engineering".to_string(),
                "6.042 Mathematics for Computer Science".to_string(),
                "6.170 Software Studio".to_string(),
            ],
            total_hours: 78,
            credits: 12,
        }
    }

    /// MIT 学习成果 / MIT learning outcomes
    fn mit_learning_outcomes() -> Vec<LearningOutcome> {
        vec![
            LearningOutcome {
                id: "LO_001".to_string(),
                description: "能够使用进程代数理论分析和设计工作流系统".to_string(),
                category: LearningCategory::Application,
                assessment_method: "项目作业和期末考试".to_string(),
            },
            LearningOutcome {
                id: "LO_002".to_string(),
                description: "理解分布式工作流系统的挑战和解决方案".to_string(),
                category: LearningCategory::Comprehension,
                assessment_method: "课堂讨论和论文".to_string(),
            },
            LearningOutcome {
                id: "LO_003".to_string(),
                description: "能够使用形式化方法验证工作流的正确性".to_string(),
                category: LearningCategory::Analysis,
                assessment_method: "实验报告和演示".to_string(),
            },
            LearningOutcome {
                id: "LO_004".to_string(),
                description: "能够分析和优化工作流系统的性能".to_string(),
                category: LearningCategory::Evaluation,
                assessment_method: "性能测试和优化报告".to_string(),
            },
        ]
    }

    /// MIT 评估标准 / MIT assessment criteria
    fn mit_assessment_criteria() -> Vec<AssessmentCriteria> {
        vec![
            AssessmentCriteria {
                id: "AC_001".to_string(),
                description: "理论理解和应用能力".to_string(),
                weight: 0.3,
                rubric: AssessmentRubric {
                    excellent: "能够深入理解理论并创新性地应用到实际问题中".to_string(),
                    good: "能够理解理论并正确应用到标准问题中".to_string(),
                    satisfactory: "基本理解理论，能够解决简单问题".to_string(),
                    needs_improvement: "理论理解不足，应用能力有限".to_string(),
                },
            },
            AssessmentCriteria {
                id: "AC_002".to_string(),
                description: "系统设计和实现能力".to_string(),
                weight: 0.4,
                rubric: AssessmentRubric {
                    excellent: "能够设计复杂系统并高质量实现".to_string(),
                    good: "能够设计合理系统并正确实现".to_string(),
                    satisfactory: "能够设计基本系统并实现核心功能".to_string(),
                    needs_improvement: "系统设计不合理，实现质量差".to_string(),
                },
            },
            AssessmentCriteria {
                id: "AC_003".to_string(),
                description: "分析和解决问题的能力".to_string(),
                weight: 0.2,
                rubric: AssessmentRubric {
                    excellent: "能够快速分析问题并提出创新解决方案".to_string(),
                    good: "能够分析问题并提出有效解决方案".to_string(),
                    satisfactory: "能够分析简单问题并提出基本解决方案".to_string(),
                    needs_improvement: "问题分析能力不足，解决方案有限".to_string(),
                },
            },
            AssessmentCriteria {
                id: "AC_004".to_string(),
                description: "沟通和表达能力".to_string(),
                weight: 0.1,
                rubric: AssessmentRubric {
                    excellent: "能够清晰表达复杂概念并有效沟通".to_string(),
                    good: "能够清楚表达概念并进行有效沟通".to_string(),
                    satisfactory: "能够基本表达概念并进行沟通".to_string(),
                    needs_improvement: "表达能力不足，沟通效果差".to_string(),
                },
            },
        ]
    }

    /// 获取课程基准测试 / Get course benchmark
    pub fn get_benchmark(&self) -> &UniversityCourseBenchmark {
        &self.benchmark
    }

    /// 评估学习成果达成度 / Assess learning outcome achievement
    pub fn assess_learning_outcome(
        &self,
        outcome_id: &str,
        student_performance: &StudentPerformance,
    ) -> AssessmentResult {
        let outcome = self
            .benchmark
            .learning_outcomes
            .iter()
            .find(|lo| lo.id == outcome_id)
            .expect("Learning outcome not found");

        let score = match outcome.category {
            LearningCategory::Knowledge => student_performance.knowledge_score,
            LearningCategory::Comprehension => student_performance.comprehension_score,
            LearningCategory::Application => student_performance.application_score,
            LearningCategory::Analysis => student_performance.analysis_score,
            LearningCategory::Synthesis => student_performance.synthesis_score,
            LearningCategory::Evaluation => student_performance.evaluation_score,
        };

        let grade = if score >= 90.0 {
            "A".to_string()
        } else if score >= 80.0 {
            "B".to_string()
        } else if score >= 70.0 {
            "C".to_string()
        } else if score >= 60.0 {
            "D".to_string()
        } else {
            "F".to_string()
        };

        AssessmentResult {
            outcome_id: outcome_id.to_string(),
            score,
            grade,
            feedback: self.generate_feedback(outcome, score),
        }
    }

    /// 生成反馈 / Generate feedback
    fn generate_feedback(&self, outcome: &LearningOutcome, score: f64) -> String {
        if score >= 90.0 {
            format!(
                "在{}方面表现优秀，达到了课程的最高标准",
                outcome.description
            )
        } else if score >= 80.0 {
            format!("在{}方面表现良好，基本达到了课程要求", outcome.description)
        } else if score >= 70.0 {
            format!("在{}方面表现一般，需要进一步改进", outcome.description)
        } else {
            format!(
                "在{}方面需要显著改进，建议加强相关学习",
                outcome.description
            )
        }
    }
}

/// Stanford 工作流课程 / Stanford Workflow Course
pub struct StanfordWorkflowCourse {
    benchmark: UniversityCourseBenchmark,
}

impl Default for StanfordWorkflowCourse {
    fn default() -> Self {
        Self::new()
    }
}

impl StanfordWorkflowCourse {
    /// 创建 Stanford 工作流课程基准测试 / Create Stanford workflow course benchmark
    pub fn new() -> Self {
        Self {
            benchmark: UniversityCourseBenchmark {
                university: "Stanford University".to_string(),
                course_name: "Distributed Systems and Workflow Management".to_string(),
                course_code: "CS 244B".to_string(),
                curriculum: Self::stanford_curriculum(),
                learning_outcomes: Self::stanford_learning_outcomes(),
                assessment_criteria: Self::stanford_assessment_criteria(),
            },
        }
    }

    /// Stanford 课程大纲 / Stanford curriculum
    fn stanford_curriculum() -> CourseCurriculum {
        CourseCurriculum {
            modules: vec![
                CourseModule {
                    id: "MOD_001".to_string(),
                    title: "Distributed Systems Fundamentals".to_string(),
                    description: "分布式系统基础概念和原理".to_string(),
                    topics: vec![
                        "Distributed Computing Models".to_string(),
                        "Consistency and Replication".to_string(),
                        "Fault Tolerance".to_string(),
                        "Distributed Algorithms".to_string(),
                    ],
                    duration_hours: 22,
                    difficulty_level: DifficultyLevel::Advanced,
                },
                CourseModule {
                    id: "MOD_002".to_string(),
                    title: "Workflow Orchestration".to_string(),
                    description: "工作流编排和调度技术".to_string(),
                    topics: vec![
                        "Workflow Scheduling".to_string(),
                        "Resource Management".to_string(),
                        "Load Balancing".to_string(),
                        "Dynamic Scaling".to_string(),
                    ],
                    duration_hours: 20,
                    difficulty_level: DifficultyLevel::Advanced,
                },
                CourseModule {
                    id: "MOD_003".to_string(),
                    title: "Event-Driven Architecture".to_string(),
                    description: "事件驱动架构和流处理".to_string(),
                    topics: vec![
                        "Event Sourcing".to_string(),
                        "CQRS Pattern".to_string(),
                        "Stream Processing".to_string(),
                        "Message Queues".to_string(),
                    ],
                    duration_hours: 18,
                    difficulty_level: DifficultyLevel::Advanced,
                },
                CourseModule {
                    id: "MOD_004".to_string(),
                    title: "Cloud-Native Workflows".to_string(),
                    description: "云原生工作流系统设计".to_string(),
                    topics: vec![
                        "Microservices Architecture".to_string(),
                        "Container Orchestration".to_string(),
                        "Service Mesh".to_string(),
                        "Serverless Computing".to_string(),
                    ],
                    duration_hours: 16,
                    difficulty_level: DifficultyLevel::Expert,
                },
            ],
            prerequisites: vec![
                "CS 110 Principles of Computer Systems".to_string(),
                "CS 161 Design and Analysis of Algorithms".to_string(),
                "CS 240 Advanced Topics in Operating Systems".to_string(),
            ],
            total_hours: 76,
            credits: 4,
        }
    }

    /// Stanford 学习成果 / Stanford learning outcomes
    fn stanford_learning_outcomes() -> Vec<LearningOutcome> {
        vec![
            LearningOutcome {
                id: "LO_001".to_string(),
                description: "理解分布式系统的设计原理和挑战".to_string(),
                category: LearningCategory::Comprehension,
                assessment_method: "期中考试和项目报告".to_string(),
            },
            LearningOutcome {
                id: "LO_002".to_string(),
                description: "能够设计和实现分布式工作流系统".to_string(),
                category: LearningCategory::Application,
                assessment_method: "编程作业和最终项目".to_string(),
            },
            LearningOutcome {
                id: "LO_003".to_string(),
                description: "掌握事件驱动架构的设计模式".to_string(),
                category: LearningCategory::Application,
                assessment_method: "设计文档和代码审查".to_string(),
            },
            LearningOutcome {
                id: "LO_004".to_string(),
                description: "能够评估和优化系统性能".to_string(),
                category: LearningCategory::Evaluation,
                assessment_method: "性能测试和优化报告".to_string(),
            },
        ]
    }

    /// Stanford 评估标准 / Stanford assessment criteria
    fn stanford_assessment_criteria() -> Vec<AssessmentCriteria> {
        vec![
            AssessmentCriteria {
                id: "AC_001".to_string(),
                description: "技术理解和实现能力".to_string(),
                weight: 0.4,
                rubric: AssessmentRubric {
                    excellent: "深入理解技术原理并能高质量实现".to_string(),
                    good: "理解技术原理并能正确实现".to_string(),
                    satisfactory: "基本理解技术原理并能实现基本功能".to_string(),
                    needs_improvement: "技术理解不足，实现质量差".to_string(),
                },
            },
            AssessmentCriteria {
                id: "AC_002".to_string(),
                description: "系统设计能力".to_string(),
                weight: 0.3,
                rubric: AssessmentRubric {
                    excellent: "能够设计复杂、可扩展的系统架构".to_string(),
                    good: "能够设计合理的系统架构".to_string(),
                    satisfactory: "能够设计基本的系统架构".to_string(),
                    needs_improvement: "系统设计能力不足".to_string(),
                },
            },
            AssessmentCriteria {
                id: "AC_003".to_string(),
                description: "问题解决和创新能力".to_string(),
                weight: 0.2,
                rubric: AssessmentRubric {
                    excellent: "能够创新性地解决复杂问题".to_string(),
                    good: "能够有效解决标准问题".to_string(),
                    satisfactory: "能够解决基本问题".to_string(),
                    needs_improvement: "问题解决能力有限".to_string(),
                },
            },
            AssessmentCriteria {
                id: "AC_004".to_string(),
                description: "团队协作和沟通能力".to_string(),
                weight: 0.1,
                rubric: AssessmentRubric {
                    excellent: "优秀的团队协作和沟通能力".to_string(),
                    good: "良好的团队协作和沟通能力".to_string(),
                    satisfactory: "基本的团队协作和沟通能力".to_string(),
                    needs_improvement: "团队协作和沟通能力需要改进".to_string(),
                },
            },
        ]
    }

    /// 获取课程基准测试 / Get course benchmark
    pub fn get_benchmark(&self) -> &UniversityCourseBenchmark {
        &self.benchmark
    }
}

/// 学生表现 / Student Performance
#[derive(Debug, Clone)]
pub struct StudentPerformance {
    pub knowledge_score: f64,
    pub comprehension_score: f64,
    pub application_score: f64,
    pub analysis_score: f64,
    pub synthesis_score: f64,
    pub evaluation_score: f64,
}

/// 评估结果 / Assessment Result
#[derive(Debug, Clone)]
pub struct AssessmentResult {
    pub outcome_id: String,
    pub score: f64,
    pub grade: String,
    pub feedback: String,
}

/// 课程对比分析 / Course Comparison Analysis
pub struct CourseComparison {
    courses: Vec<UniversityCourseBenchmark>,
}

impl Default for CourseComparison {
    fn default() -> Self {
        Self::new()
    }
}

impl CourseComparison {
    /// 创建课程对比 / Create course comparison
    pub fn new() -> Self {
        Self {
            courses: Vec::new(),
        }
    }

    /// 添加课程 / Add course
    pub fn add_course(&mut self, course: UniversityCourseBenchmark) {
        self.courses.push(course);
    }

    /// 生成对比报告 / Generate comparison report
    pub fn generate_comparison_report(&self) -> CourseComparisonReport {
        let mut report = CourseComparisonReport {
            courses: Vec::new(),
            common_topics: Vec::new(),
            unique_topics: HashMap::new(),
            recommendations: Vec::new(),
        };

        // 分析共同主题 / Analyze common topics
        report.common_topics = self.find_common_topics();

        // 分析独特主题 / Analyze unique topics
        report.unique_topics = self.find_unique_topics();

        // 生成建议 / Generate recommendations
        report.recommendations = self.generate_recommendations();

        // 添加课程信息 / Add course information
        for course in &self.courses {
            report.courses.push(CourseSummary {
                university: course.university.clone(),
                course_name: course.course_name.clone(),
                total_hours: course.curriculum.total_hours,
                credits: course.curriculum.credits,
                difficulty_level: self.calculate_average_difficulty(course),
            });
        }

        report
    }

    /// 查找共同主题 / Find common topics
    fn find_common_topics(&self) -> Vec<String> {
        if self.courses.is_empty() {
            return Vec::new();
        }

        let mut common_topics = Vec::new();
        let first_course_topics: std::collections::HashSet<String> = self.courses[0]
            .curriculum
            .modules
            .iter()
            .flat_map(|module| module.topics.clone())
            .collect();

        for topic in first_course_topics {
            if self.courses.iter().all(|course| {
                course
                    .curriculum
                    .modules
                    .iter()
                    .any(|module| module.topics.contains(&topic))
            }) {
                common_topics.push(topic);
            }
        }

        common_topics
    }

    /// 查找独特主题 / Find unique topics
    fn find_unique_topics(&self) -> HashMap<String, Vec<String>> {
        let mut unique_topics = HashMap::new();

        for course in &self.courses {
            let course_topics: std::collections::HashSet<String> = course
                .curriculum
                .modules
                .iter()
                .flat_map(|module| module.topics.clone())
                .collect();

            let other_topics: std::collections::HashSet<String> = self
                .courses
                .iter()
                .filter(|c| c.university != course.university)
                .flat_map(|c| c.curriculum.modules.iter())
                .flat_map(|module| module.topics.clone())
                .collect();

            let unique: Vec<String> = course_topics.difference(&other_topics).cloned().collect();

            if !unique.is_empty() {
                unique_topics.insert(course.university.clone(), unique);
            }
        }

        unique_topics
    }

    /// 计算平均难度 / Calculate average difficulty
    fn calculate_average_difficulty(&self, course: &UniversityCourseBenchmark) -> f64 {
        let total_hours: u32 = course
            .curriculum
            .modules
            .iter()
            .map(|module| module.duration_hours)
            .sum();

        let weighted_difficulty: u32 = course
            .curriculum
            .modules
            .iter()
            .map(|module| {
                let difficulty_value = match module.difficulty_level {
                    DifficultyLevel::Beginner => 1,
                    DifficultyLevel::Intermediate => 2,
                    DifficultyLevel::Advanced => 3,
                    DifficultyLevel::Expert => 4,
                };
                difficulty_value * module.duration_hours
            })
            .sum();

        if total_hours > 0 {
            weighted_difficulty as f64 / total_hours as f64
        } else {
            0.0
        }
    }

    /// 生成建议 / Generate recommendations
    fn generate_recommendations(&self) -> Vec<String> {
        let mut recommendations = Vec::new();

        if self.courses.len() >= 2 {
            recommendations.push("建议结合多所大学的课程内容，形成更全面的知识体系".to_string());
        }

        let common_topics = self.find_common_topics();
        if common_topics.len() > 5 {
            recommendations.push("共同主题较多，建议重点关注这些核心概念".to_string());
        }

        recommendations.push("建议根据学习目标选择合适的课程难度级别".to_string());
        recommendations.push("建议结合实际项目来巩固理论知识".to_string());

        recommendations
    }
}

/// 课程总结 / Course Summary
#[derive(Debug, Clone)]
pub struct CourseSummary {
    pub university: String,
    pub course_name: String,
    pub total_hours: u32,
    pub credits: u8,
    pub difficulty_level: f64,
}

/// 课程对比报告 / Course Comparison Report
#[derive(Debug, Clone)]
pub struct CourseComparisonReport {
    pub courses: Vec<CourseSummary>,
    pub common_topics: Vec<String>,
    pub unique_topics: HashMap<String, Vec<String>>,
    pub recommendations: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mit_workflow_course() {
        let mit_course = MITWorkflowCourse::new();
        let benchmark = mit_course.get_benchmark();

        assert_eq!(
            benchmark.university,
            "Massachusetts Institute of Technology"
        );
        assert_eq!(benchmark.course_code, "6.824");
        assert!(!benchmark.curriculum.modules.is_empty());
        assert!(!benchmark.learning_outcomes.is_empty());
    }

    #[test]
    fn test_stanford_workflow_course() {
        let stanford_course = StanfordWorkflowCourse::new();
        let benchmark = stanford_course.get_benchmark();

        assert_eq!(benchmark.university, "Stanford University");
        assert_eq!(benchmark.course_code, "CS 244B");
        assert!(!benchmark.curriculum.modules.is_empty());
        assert!(!benchmark.learning_outcomes.is_empty());
    }

    #[test]
    fn test_course_comparison() {
        let mut comparison = CourseComparison::new();

        let mit_course = MITWorkflowCourse::new();
        let stanford_course = StanfordWorkflowCourse::new();

        comparison.add_course(mit_course.get_benchmark().clone());
        comparison.add_course(stanford_course.get_benchmark().clone());

        let report = comparison.generate_comparison_report();

        assert_eq!(report.courses.len(), 2);
        assert!(!report.recommendations.is_empty());
    }

    #[test]
    fn test_learning_outcome_assessment() {
        let mit_course = MITWorkflowCourse::new();
        let student_performance = StudentPerformance {
            knowledge_score: 85.0,
            comprehension_score: 90.0,
            application_score: 88.0,
            analysis_score: 82.0,
            synthesis_score: 80.0,
            evaluation_score: 85.0,
        };

        let result = mit_course.assess_learning_outcome("LO_001", &student_performance);

        assert_eq!(result.outcome_id, "LO_001");
        assert!(result.score > 0.0);
        assert!(!result.grade.is_empty());
        assert!(!result.feedback.is_empty());
    }
}
