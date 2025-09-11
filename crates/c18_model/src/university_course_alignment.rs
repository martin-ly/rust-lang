//! 大学课程对标实现
//! 
//! 本模块实现了与国际著名大学课程的对标分析，
//! 包括 MIT、CMU、Stanford、Berkeley、ETH Zurich 等大学的课程内容。

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use thiserror::Error;

/// 课程对标错误类型
#[derive(Error, Debug)]
pub enum CourseAlignmentError {
    #[error("课程不存在: {0}")]
    CourseNotFound(String),
    
    #[error("主题不存在: {0}")]
    TopicNotFound(String),
    
    #[error("映射失败: {0}")]
    MappingFailed(String),
}

/// 大学标识
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum University {
    // 现有大学
    MIT,
    CMU,
    Stanford,
    Berkeley,
    ETHZurich,
    
    // 美国大学
    Harvard,
    Princeton,
    Yale,
    Columbia,
    Cornell,
    GeorgiaTech,
    UIUC,
    UW,
    UTAustin,
    UCSD,
    
    // 英国大学
    Oxford,
    Cambridge,
    ImperialCollege,
    UCL,
    Edinburgh,
    Manchester,
    Bristol,
    Southampton,
    
    // 欧洲大学
    TUDelft,
    KTH,
    EPFL,
    TUM,
    TUVienna,
    
    // 亚洲大学
    TokyoUniversity,
    SeoulNationalUniversity,
    NUS,
    HKUST,
    KAIST,
    NTU,
    CUHK,
}

/// 评估方法
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum AssessmentMethod {
    WrittenExam,
    ProgrammingAssignment,
    Project,
    Presentation,
    PeerReview,
    LabWork,
    Quiz,
}

/// 课程主题
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CourseTopic {
    pub id: String,
    pub name: String,
    pub description: String,
    pub learning_objectives: Vec<String>,
    pub prerequisites: Vec<String>,
    pub assessment_methods: Vec<AssessmentMethod>,
    pub rust_concepts: Vec<String>,
}

/// 大学课程
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UniversityCourse {
    pub university: University,
    pub course_code: String,
    pub course_name: String,
    pub credits: u8,
    pub topics: Vec<CourseTopic>,
    pub learning_outcomes: Vec<String>,
    pub prerequisites: Vec<String>,
}

/// 课程对标分析器
pub struct CourseAlignmentAnalyzer {
    courses: HashMap<String, UniversityCourse>,
    topic_mappings: HashMap<String, Vec<String>>,
}

impl CourseAlignmentAnalyzer {
    /// 创建新的课程对标分析器
    pub fn new() -> Self {
        let mut courses = HashMap::new();
        let mut topic_mappings = HashMap::new();

        // 初始化课程
        // 现有课程
        courses.insert("MIT_6_031".to_string(), Self::mit_6_031());
        courses.insert("CMU_15_214".to_string(), Self::cmu_15_214());
        courses.insert("Stanford_CS_240".to_string(), Self::stanford_cs_240());
        courses.insert("Berkeley_CS_169".to_string(), Self::berkeley_cs_169());
        courses.insert("ETH_252_0216".to_string(), Self::eth_252_0216());
        
        // 新增美国大学课程
        courses.insert("Harvard_CS_50".to_string(), Self::harvard_cs_50());
        courses.insert("Princeton_COS_333".to_string(), Self::princeton_cos_333());
        courses.insert("Yale_CPSC_323".to_string(), Self::yale_cpsc_323());
        courses.insert("Columbia_CS_3157".to_string(), Self::columbia_cs_3157());
        courses.insert("Cornell_CS_3110".to_string(), Self::cornell_cs_3110());
        
        // 新增英国大学课程
        courses.insert("Oxford_CS_204".to_string(), Self::oxford_cs_204());
        courses.insert("Cambridge_CS_75".to_string(), Self::cambridge_cs_75());
        courses.insert("Imperial_CS_400".to_string(), Self::imperial_cs_400());
        courses.insert("UCL_CS_301".to_string(), Self::ucl_cs_301());
        courses.insert("Edinburgh_CS_301".to_string(), Self::edinburgh_cs_301());
        
        // 新增欧洲大学课程
        courses.insert("TUDelft_CS_4055".to_string(), Self::tu_delft_cs_4055());
        courses.insert("KTH_CS_2440".to_string(), Self::kth_cs_2440());
        courses.insert("EPFL_CS_210".to_string(), Self::epfl_cs_210());
        courses.insert("TUM_CS_2050".to_string(), Self::tum_cs_2050());
        
        // 新增亚洲大学课程
        courses.insert("Tokyo_CS_353".to_string(), Self::tokyo_cs_353());
        courses.insert("SNU_CS_431".to_string(), Self::snu_cs_431());
        courses.insert("NUS_CS_3219".to_string(), Self::nus_cs_3219());
        courses.insert("HKUST_CS_342".to_string(), Self::hkust_cs_342());
        
        // 2025年新增课程 - 暂时注释，待实现
        // courses.insert("GT_CS_6310".to_string(), Self::georgia_tech_cs_6310());
        // courses.insert("UIUC_CS_427".to_string(), Self::uiuc_cs_427());
        // courses.insert("UW_CS_403".to_string(), Self::uw_cs_403());
        // courses.insert("UT_Austin_CS_373".to_string(), Self::ut_austin_cs_373());
        // courses.insert("UCSD_CSE_110".to_string(), Self::ucsd_cse_110());
        
        // courses.insert("Manchester_CS_20411".to_string(), Self::manchester_cs_20411());
        // courses.insert("Bristol_CS_20006".to_string(), Self::bristol_cs_20006());
        // courses.insert("Southampton_CS_2001".to_string(), Self::southampton_cs_2001());
        
        // courses.insert("TUM_CS_2050".to_string(), Self::tum_cs_2050());
        // courses.insert("TU_Vienna_CS_188_705".to_string(), Self::tu_vienna_cs_188_705());
        
        // courses.insert("KAIST_CS_341".to_string(), Self::kaist_cs_341());
        // courses.insert("NTU_CS_3219".to_string(), Self::ntu_cs_3219());
        // courses.insert("CUHK_CS_342".to_string(), Self::cuhk_cs_342());

        // 初始化主题映射
        topic_mappings.insert("specifications".to_string(), vec![
            "trait_bounds".to_string(),
            "documentation".to_string(),
            "type_system".to_string(),
            "contracts".to_string(),
        ]);
        
        topic_mappings.insert("testing".to_string(), vec![
            "unit_tests".to_string(),
            "integration_tests".to_string(),
            "property_based_testing".to_string(),
            "test_organization".to_string(),
        ]);
        
        topic_mappings.insert("design_patterns".to_string(), vec![
            "trait_objects".to_string(),
            "enum_patterns".to_string(),
            "builder_pattern".to_string(),
            "strategy_pattern".to_string(),
        ]);
        
        topic_mappings.insert("object_oriented_design".to_string(), vec![
            "traits".to_string(),
            "structs".to_string(),
            "enums".to_string(),
            "generics".to_string(),
        ]);
        
        topic_mappings.insert("software_architecture".to_string(), vec![
            "modules".to_string(),
            "crates".to_string(),
            "workspaces".to_string(),
            "dependency_management".to_string(),
        ]);

        Self {
            courses,
            topic_mappings,
        }
    }

    /// 获取课程
    pub fn get_course(&self, course_id: &str) -> Result<&UniversityCourse, CourseAlignmentError> {
        self.courses.get(course_id)
            .ok_or_else(|| CourseAlignmentError::CourseNotFound(course_id.to_string()))
    }

    /// 获取所有课程
    pub fn get_all_courses(&self) -> Vec<&UniversityCourse> {
        self.courses.values().collect()
    }

    /// 根据大学获取课程
    pub fn get_courses_by_university(&self, university: University) -> Vec<&UniversityCourse> {
        self.courses.values()
            .filter(|course| course.university == university)
            .collect()
    }

    /// 获取主题的 Rust 概念映射
    pub fn get_rust_concepts(&self, topic: &str) -> Result<&Vec<String>, CourseAlignmentError> {
        self.topic_mappings.get(topic)
            .ok_or_else(|| CourseAlignmentError::TopicNotFound(topic.to_string()))
    }

    /// 分析课程与 Rust 的对齐度
    pub fn analyze_alignment(&self, course_id: &str) -> Result<CourseAlignmentAnalysis, CourseAlignmentError> {
        let course = self.get_course(course_id)?;
        let mut total_topics = 0;
        let mut mapped_topics = 0;
        let mut rust_concepts = Vec::new();

        for topic in &course.topics {
            total_topics += 1;
            if let Ok(concepts) = self.get_rust_concepts(&topic.id) {
                mapped_topics += 1;
                rust_concepts.extend(concepts.clone());
            }
        }

        let alignment_score = if total_topics > 0 {
            (mapped_topics as f64 / total_topics as f64) * 100.0
        } else {
            0.0
        };

        Ok(CourseAlignmentAnalysis {
            course_id: course_id.to_string(),
            university: course.university.clone(),
            course_name: course.course_name.clone(),
            alignment_score,
            total_topics,
            mapped_topics,
            rust_concepts,
            recommendations: self.generate_recommendations(course, alignment_score),
        })
    }

    /// 生成学习建议
    fn generate_recommendations(&self, course: &UniversityCourse, alignment_score: f64) -> Vec<String> {
        let mut recommendations = Vec::new();

        if alignment_score < 50.0 {
            recommendations.push("建议先学习 Rust 基础语法和所有权系统".to_string());
        } else if alignment_score < 80.0 {
            recommendations.push("建议深入学习 Rust 的高级特性".to_string());
        } else {
            recommendations.push("可以开始实践项目，应用所学概念".to_string());
        }

        recommendations.push(format!("重点关注 {} 的核心主题", course.course_name));
        recommendations.push("建议结合实际项目进行学习".to_string());

        recommendations
    }

    /// MIT 6.031 - Software Construction
    fn mit_6_031() -> UniversityCourse {
        UniversityCourse {
            university: University::MIT,
            course_code: "6.031".to_string(),
            course_name: "Software Construction".to_string(),
            credits: 12,
            topics: vec![
                CourseTopic {
                    id: "specifications".to_string(),
                    name: "Specifications".to_string(),
                    description: "Writing clear and precise specifications".to_string(),
                    learning_objectives: vec![
                        "Write clear specifications".to_string(),
                        "Understand preconditions and postconditions".to_string(),
                        "Use assertions effectively".to_string(),
                    ],
                    prerequisites: vec!["Basic programming".to_string()],
                    assessment_methods: vec![AssessmentMethod::ProgrammingAssignment],
                    rust_concepts: vec![
                        "trait_bounds".to_string(),
                        "documentation".to_string(),
                        "type_system".to_string(),
                    ],
                },
                CourseTopic {
                    id: "testing".to_string(),
                    name: "Testing".to_string(),
                    description: "Systematic testing strategies".to_string(),
                    learning_objectives: vec![
                        "Design comprehensive test suites".to_string(),
                        "Understand test coverage".to_string(),
                        "Write effective unit tests".to_string(),
                    ],
                    prerequisites: vec!["Specifications".to_string()],
                    assessment_methods: vec![AssessmentMethod::ProgrammingAssignment],
                    rust_concepts: vec![
                        "unit_tests".to_string(),
                        "integration_tests".to_string(),
                        "test_organization".to_string(),
                    ],
                },
                CourseTopic {
                    id: "abstract_data_types".to_string(),
                    name: "Abstract Data Types".to_string(),
                    description: "Design and implementation of ADTs".to_string(),
                    learning_objectives: vec![
                        "Design effective ADTs".to_string(),
                        "Implement ADTs correctly".to_string(),
                        "Use ADTs in practice".to_string(),
                    ],
                    prerequisites: vec!["Testing".to_string()],
                    assessment_methods: vec![AssessmentMethod::ProgrammingAssignment],
                    rust_concepts: vec![
                        "structs".to_string(),
                        "enums".to_string(),
                        "traits".to_string(),
                    ],
                },
                CourseTopic {
                    id: "design_patterns".to_string(),
                    name: "Design Patterns".to_string(),
                    description: "Common design patterns and their applications".to_string(),
                    learning_objectives: vec![
                        "Understand common design patterns".to_string(),
                        "Apply patterns appropriately".to_string(),
                        "Recognize pattern opportunities".to_string(),
                    ],
                    prerequisites: vec!["Abstract Data Types".to_string()],
                    assessment_methods: vec![AssessmentMethod::Project],
                    rust_concepts: vec![
                        "trait_objects".to_string(),
                        "enum_patterns".to_string(),
                        "builder_pattern".to_string(),
                    ],
                },
            ],
            learning_outcomes: vec![
                "Write clear and precise specifications".to_string(),
                "Design comprehensive test suites".to_string(),
                "Apply software engineering principles".to_string(),
                "Use design patterns effectively".to_string(),
            ],
            prerequisites: vec!["6.0001 Introduction to Computer Science".to_string()],
        }
    }

    /// CMU 15-214 - Principles of Software Construction
    fn cmu_15_214() -> UniversityCourse {
        UniversityCourse {
            university: University::CMU,
            course_code: "15-214".to_string(),
            course_name: "Principles of Software Construction".to_string(),
            credits: 12,
            topics: vec![
                CourseTopic {
                    id: "object_oriented_design".to_string(),
                    name: "Object-Oriented Design".to_string(),
                    description: "Design principles and patterns".to_string(),
                    learning_objectives: vec![
                        "Apply SOLID principles".to_string(),
                        "Use design patterns effectively".to_string(),
                        "Design maintainable code".to_string(),
                    ],
                    prerequisites: vec!["Java programming".to_string()],
                    assessment_methods: vec![AssessmentMethod::Project],
                    rust_concepts: vec![
                        "traits".to_string(),
                        "structs".to_string(),
                        "enums".to_string(),
                        "generics".to_string(),
                    ],
                },
                CourseTopic {
                    id: "concurrency".to_string(),
                    name: "Concurrency".to_string(),
                    description: "Concurrent programming concepts".to_string(),
                    learning_objectives: vec![
                        "Understand concurrency models".to_string(),
                        "Write thread-safe code".to_string(),
                        "Avoid common concurrency pitfalls".to_string(),
                    ],
                    prerequisites: vec!["Object-Oriented Design".to_string()],
                    assessment_methods: vec![AssessmentMethod::ProgrammingAssignment],
                    rust_concepts: vec![
                        "threads".to_string(),
                        "async_await".to_string(),
                        "channels".to_string(),
                        "mutex".to_string(),
                    ],
                },
            ],
            learning_outcomes: vec![
                "Apply object-oriented design principles".to_string(),
                "Use design patterns effectively".to_string(),
                "Write concurrent programs safely".to_string(),
            ],
            prerequisites: vec!["15-112 Fundamentals of Programming".to_string()],
        }
    }

    /// Stanford CS 240 - Advanced Software Engineering
    fn stanford_cs_240() -> UniversityCourse {
        UniversityCourse {
            university: University::Stanford,
            course_code: "CS 240".to_string(),
            course_name: "Advanced Software Engineering".to_string(),
            credits: 3,
            topics: vec![
                CourseTopic {
                    id: "software_architecture".to_string(),
                    name: "Software Architecture".to_string(),
                    description: "Architectural patterns and design".to_string(),
                    learning_objectives: vec![
                        "Understand architectural patterns".to_string(),
                        "Design scalable systems".to_string(),
                        "Evaluate architectural decisions".to_string(),
                    ],
                    prerequisites: vec!["Software engineering basics".to_string()],
                    assessment_methods: vec![AssessmentMethod::Project],
                    rust_concepts: vec![
                        "modules".to_string(),
                        "crates".to_string(),
                        "workspaces".to_string(),
                        "dependency_management".to_string(),
                    ],
                },
            ],
            learning_outcomes: vec![
                "Design software architectures".to_string(),
                "Apply architectural patterns".to_string(),
                "Evaluate system designs".to_string(),
            ],
            prerequisites: vec!["CS 106B Programming Abstractions".to_string()],
        }
    }

    /// Berkeley CS 169 - Software Engineering
    fn berkeley_cs_169() -> UniversityCourse {
        UniversityCourse {
            university: University::Berkeley,
            course_code: "CS 169".to_string(),
            course_name: "Software Engineering".to_string(),
            credits: 4,
            topics: vec![
                CourseTopic {
                    id: "agile_methodologies".to_string(),
                    name: "Agile Methodologies".to_string(),
                    description: "Agile development practices".to_string(),
                    learning_objectives: vec![
                        "Apply agile methodologies".to_string(),
                        "Work in development teams".to_string(),
                        "Use version control effectively".to_string(),
                    ],
                    prerequisites: vec!["Programming experience".to_string()],
                    assessment_methods: vec![AssessmentMethod::Project],
                    rust_concepts: vec![
                        "cargo".to_string(),
                        "git_integration".to_string(),
                        "testing".to_string(),
                        "documentation".to_string(),
                    ],
                },
            ],
            learning_outcomes: vec![
                "Apply agile development practices".to_string(),
                "Work effectively in teams".to_string(),
                "Use modern development tools".to_string(),
            ],
            prerequisites: vec!["CS 61B Data Structures".to_string()],
        }
    }

    /// ETH Zurich 252-0216-00 - Software Architecture
    fn eth_252_0216() -> UniversityCourse {
        UniversityCourse {
            university: University::ETHZurich,
            course_code: "252-0216-00".to_string(),
            course_name: "Software Architecture".to_string(),
            credits: 7,
            topics: vec![
                CourseTopic {
                    id: "architectural_patterns".to_string(),
                    name: "Architectural Patterns".to_string(),
                    description: "Common architectural patterns".to_string(),
                    learning_objectives: vec![
                        "Understand architectural patterns".to_string(),
                        "Apply patterns in practice".to_string(),
                        "Evaluate pattern effectiveness".to_string(),
                    ],
                    prerequisites: vec!["Software engineering".to_string()],
                    assessment_methods: vec![AssessmentMethod::WrittenExam],
                    rust_concepts: vec![
                        "layered_architecture".to_string(),
                        "microservices".to_string(),
                        "event_driven".to_string(),
                        "plugin_architecture".to_string(),
                    ],
                },
            ],
            learning_outcomes: vec![
                "Understand architectural patterns".to_string(),
                "Apply patterns in practice".to_string(),
                "Design maintainable architectures".to_string(),
            ],
            prerequisites: vec!["252-0215-00 Software Engineering".to_string()],
        }
    }

    /// Harvard CS 50 - Introduction to Computer Science
    fn harvard_cs_50() -> UniversityCourse {
        UniversityCourse {
            university: University::Harvard,
            course_code: "CS 50".to_string(),
            course_name: "Introduction to Computer Science".to_string(),
            credits: 4,
            topics: vec![
                CourseTopic {
                    id: "programming_fundamentals".to_string(),
                    name: "Programming Fundamentals".to_string(),
                    description: "Basic programming concepts and problem solving".to_string(),
                    learning_objectives: vec![
                        "Learn programming fundamentals".to_string(),
                        "Develop problem-solving skills".to_string(),
                        "Understand algorithms and data structures".to_string(),
                    ],
                    prerequisites: vec!["No prerequisites".to_string()],
                    assessment_methods: vec![AssessmentMethod::ProgrammingAssignment, AssessmentMethod::Quiz],
                    rust_concepts: vec![
                        "basic_syntax".to_string(),
                        "variables".to_string(),
                        "control_flow".to_string(),
                        "functions".to_string(),
                    ],
                },
            ],
            learning_outcomes: vec![
                "Master programming fundamentals".to_string(),
                "Develop computational thinking".to_string(),
                "Apply algorithms to solve problems".to_string(),
            ],
            prerequisites: vec![],
        }
    }

    /// Oxford CS 204 - Software Engineering
    fn oxford_cs_204() -> UniversityCourse {
        UniversityCourse {
            university: University::Oxford,
            course_code: "CS 204".to_string(),
            course_name: "Software Engineering".to_string(),
            credits: 8,
            topics: vec![
                CourseTopic {
                    id: "software_development_lifecycle".to_string(),
                    name: "Software Development Lifecycle".to_string(),
                    description: "Complete software development process".to_string(),
                    learning_objectives: vec![
                        "Understand SDLC phases".to_string(),
                        "Apply development methodologies".to_string(),
                        "Manage software projects".to_string(),
                    ],
                    prerequisites: vec!["Programming experience".to_string()],
                    assessment_methods: vec![AssessmentMethod::Project, AssessmentMethod::WrittenExam],
                    rust_concepts: vec![
                        "cargo".to_string(),
                        "testing".to_string(),
                        "documentation".to_string(),
                        "version_control".to_string(),
                    ],
                },
            ],
            learning_outcomes: vec![
                "Master software development lifecycle".to_string(),
                "Apply engineering principles".to_string(),
                "Lead software projects".to_string(),
            ],
            prerequisites: vec!["CS 101 Programming".to_string()],
        }
    }

    /// Tokyo University CS 353 - Software Engineering
    fn tokyo_cs_353() -> UniversityCourse {
        UniversityCourse {
            university: University::TokyoUniversity,
            course_code: "CS 353".to_string(),
            course_name: "Software Engineering".to_string(),
            credits: 3,
            topics: vec![
                CourseTopic {
                    id: "quality_assurance".to_string(),
                    name: "Quality Assurance".to_string(),
                    description: "Software quality and testing methodologies".to_string(),
                    learning_objectives: vec![
                        "Understand quality metrics".to_string(),
                        "Design test strategies".to_string(),
                        "Implement quality processes".to_string(),
                    ],
                    prerequisites: vec!["Software engineering basics".to_string()],
                    assessment_methods: vec![AssessmentMethod::ProgrammingAssignment, AssessmentMethod::Project],
                    rust_concepts: vec![
                        "unit_tests".to_string(),
                        "integration_tests".to_string(),
                        "property_based_testing".to_string(),
                        "benchmarking".to_string(),
                    ],
                },
            ],
            learning_outcomes: vec![
                "Master quality assurance techniques".to_string(),
                "Design comprehensive test suites".to_string(),
                "Implement quality processes".to_string(),
            ],
            prerequisites: vec!["CS 252 Data Structures".to_string()],
        }
    }

    // 其他新增课程的简化实现
    fn princeton_cos_333() -> UniversityCourse {
        UniversityCourse {
            university: University::Princeton,
            course_code: "COS 333".to_string(),
            course_name: "Advanced Programming Techniques".to_string(),
            credits: 3,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn yale_cpsc_323() -> UniversityCourse {
        UniversityCourse {
            university: University::Yale,
            course_code: "CPSC 323".to_string(),
            course_name: "Systems Programming and Computer Organization".to_string(),
            credits: 1,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn columbia_cs_3157() -> UniversityCourse {
        UniversityCourse {
            university: University::Columbia,
            course_code: "CS 3157".to_string(),
            course_name: "Advanced Programming".to_string(),
            credits: 3,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn cornell_cs_3110() -> UniversityCourse {
        UniversityCourse {
            university: University::Cornell,
            course_code: "CS 3110".to_string(),
            course_name: "Data Structures and Functional Programming".to_string(),
            credits: 4,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn cambridge_cs_75() -> UniversityCourse {
        UniversityCourse {
            university: University::Cambridge,
            course_code: "CS 75".to_string(),
            course_name: "Software Engineering".to_string(),
            credits: 16,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn imperial_cs_400() -> UniversityCourse {
        UniversityCourse {
            university: University::ImperialCollege,
            course_code: "CS 400".to_string(),
            course_name: "Software Engineering".to_string(),
            credits: 15,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn ucl_cs_301() -> UniversityCourse {
        UniversityCourse {
            university: University::UCL,
            course_code: "CS 301".to_string(),
            course_name: "Software Engineering".to_string(),
            credits: 15,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn edinburgh_cs_301() -> UniversityCourse {
        UniversityCourse {
            university: University::Edinburgh,
            course_code: "CS 301".to_string(),
            course_name: "Software Engineering".to_string(),
            credits: 20,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn tu_delft_cs_4055() -> UniversityCourse {
        UniversityCourse {
            university: University::TUDelft,
            course_code: "CS 4055".to_string(),
            course_name: "Software Architecture".to_string(),
            credits: 5,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn kth_cs_2440() -> UniversityCourse {
        UniversityCourse {
            university: University::KTH,
            course_code: "CS 2440".to_string(),
            course_name: "Software Engineering".to_string(),
            credits: 6,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn epfl_cs_210() -> UniversityCourse {
        UniversityCourse {
            university: University::EPFL,
            course_code: "CS 210".to_string(),
            course_name: "Software Engineering".to_string(),
            credits: 6,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn tum_cs_2050() -> UniversityCourse {
        UniversityCourse {
            university: University::TUM,
            course_code: "CS 2050".to_string(),
            course_name: "Software Engineering".to_string(),
            credits: 6,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn snu_cs_431() -> UniversityCourse {
        UniversityCourse {
            university: University::SeoulNationalUniversity,
            course_code: "CS 431".to_string(),
            course_name: "Software Engineering".to_string(),
            credits: 3,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn nus_cs_3219() -> UniversityCourse {
        UniversityCourse {
            university: University::NUS,
            course_code: "CS 3219".to_string(),
            course_name: "Software Engineering".to_string(),
            credits: 4,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }

    fn hkust_cs_342() -> UniversityCourse {
        UniversityCourse {
            university: University::HKUST,
            course_code: "CS 342".to_string(),
            course_name: "Software Engineering".to_string(),
            credits: 3,
            topics: vec![],
            learning_outcomes: vec![],
            prerequisites: vec![],
        }
    }
}

/// 课程对标分析结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CourseAlignmentAnalysis {
    pub course_id: String,
    pub university: University,
    pub course_name: String,
    pub alignment_score: f64,
    pub total_topics: usize,
    pub mapped_topics: usize,
    pub rust_concepts: Vec<String>,
    pub recommendations: Vec<String>,
}

/// 学习路径规划器
pub struct LearningPathPlanner {
    analyzer: CourseAlignmentAnalyzer,
}

impl LearningPathPlanner {
    /// 创建新的学习路径规划器
    pub fn new() -> Self {
        Self {
            analyzer: CourseAlignmentAnalyzer::new(),
        }
    }

    /// 生成学习路径
    pub fn generate_learning_path(&self, target_course: &str) -> Result<LearningPath, CourseAlignmentError> {
        let analysis = self.analyzer.analyze_alignment(target_course)?;
        let course = self.analyzer.get_course(target_course)?;

        let mut phases = Vec::new();
        let mut current_phase = 1;

        // 基础阶段
        phases.push(LearningPhase {
            phase_number: current_phase,
            name: "基础阶段".to_string(),
            description: "掌握 Rust 基础语法和核心概念".to_string(),
            topics: vec![
                "ownership".to_string(),
                "borrowing".to_string(),
                "lifetimes".to_string(),
                "basic_types".to_string(),
            ],
            estimated_duration: "2-3 周".to_string(),
            prerequisites: vec!["编程基础".to_string()],
        });
        current_phase += 1;

        // 进阶阶段
        phases.push(LearningPhase {
            phase_number: current_phase,
            name: "进阶阶段".to_string(),
            description: "学习高级特性和设计模式".to_string(),
            topics: analysis.rust_concepts.clone(),
            estimated_duration: "4-6 周".to_string(),
            prerequisites: vec!["基础阶段完成".to_string()],
        });
        current_phase += 1;

        // 实践阶段
        phases.push(LearningPhase {
            phase_number: current_phase,
            name: "实践阶段".to_string(),
            description: "通过项目实践应用所学知识".to_string(),
            topics: vec![
                "project_implementation".to_string(),
                "testing_practices".to_string(),
                "documentation".to_string(),
                "code_review".to_string(),
            ],
            estimated_duration: "6-8 周".to_string(),
            prerequisites: vec!["进阶阶段完成".to_string()],
        });

        Ok(LearningPath {
            target_course: target_course.to_string(),
            university: course.university.clone(),
            total_phases: phases.len(),
            phases,
            estimated_total_duration: "12-17 周".to_string(),
            prerequisites: course.prerequisites.clone(),
        })
    }
}

/// 学习阶段
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LearningPhase {
    pub phase_number: usize,
    pub name: String,
    pub description: String,
    pub topics: Vec<String>,
    pub estimated_duration: String,
    pub prerequisites: Vec<String>,
}

/// 学习路径
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LearningPath {
    pub target_course: String,
    pub university: University,
    pub total_phases: usize,
    pub phases: Vec<LearningPhase>,
    pub estimated_total_duration: String,
    pub prerequisites: Vec<String>,
}

impl Default for CourseAlignmentAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl Default for LearningPathPlanner {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_course_analyzer_creation() {
        let analyzer = CourseAlignmentAnalyzer::new();
        assert_eq!(analyzer.get_all_courses().len(), 23);
    }

    #[test]
    fn test_get_course() {
        let analyzer = CourseAlignmentAnalyzer::new();
        let course = analyzer.get_course("MIT_6_031");
        assert!(course.is_ok());
        assert_eq!(course.unwrap().university, University::MIT);
    }

    #[test]
    fn test_get_rust_concepts() {
        let analyzer = CourseAlignmentAnalyzer::new();
        let concepts = analyzer.get_rust_concepts("specifications");
        assert!(concepts.is_ok());
        assert!(!concepts.unwrap().is_empty());
    }

    #[test]
    fn test_analyze_alignment() {
        let analyzer = CourseAlignmentAnalyzer::new();
        let analysis = analyzer.analyze_alignment("MIT_6_031");
        assert!(analysis.is_ok());
        
        let result = analysis.unwrap();
        assert_eq!(result.university, University::MIT);
        assert!(result.alignment_score >= 0.0 && result.alignment_score <= 100.0);
    }

    #[test]
    fn test_learning_path_planner() {
        let planner = LearningPathPlanner::new();
        let path = planner.generate_learning_path("MIT_6_031");
        assert!(path.is_ok());
        
        let learning_path = path.unwrap();
        assert_eq!(learning_path.university, University::MIT);
        assert!(learning_path.total_phases >= 3);
    }
}
