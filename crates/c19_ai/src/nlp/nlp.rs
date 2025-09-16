// 自然语言处理模块
// Natural Language Processing Module

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 文本预处理工具
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TextPreprocessor {
    pub vocabulary: HashMap<String, usize>,
    pub max_vocab_size: usize,
    pub min_word_freq: usize,
}

impl TextPreprocessor {
    /// 创建新的文本预处理器
    pub fn new(max_vocab_size: usize, min_word_freq: usize) -> Self {
        Self {
            vocabulary: HashMap::new(),
            max_vocab_size,
            min_word_freq,
        }
    }

    /// 构建词汇表
    pub fn build_vocabulary(&mut self, texts: &[String]) {
        let mut word_counts: HashMap<String, usize> = HashMap::new();

        // 统计词频
        for text in texts {
            let words = self.tokenize(text);
            for word in words {
                *word_counts.entry(word).or_insert(0) += 1;
            }
        }

        // 过滤低频词并构建词汇表
        let mut vocab_items: Vec<_> = word_counts
            .into_iter()
            .filter(|(_, count)| *count >= self.min_word_freq)
            .collect();

        vocab_items.sort_by(|a, b| b.1.cmp(&a.1));

        for (i, (word, _)) in vocab_items.iter().take(self.max_vocab_size).enumerate() {
            self.vocabulary.insert(word.clone(), i);
        }
    }

    /// 分词
    pub fn tokenize(&self, text: &str) -> Vec<String> {
        text.to_lowercase()
            .split_whitespace()
            .map(|s| s.trim_matches(|c: char| !c.is_alphanumeric()))
            .filter(|s| !s.is_empty())
            .map(|s| s.to_string())
            .collect()
    }

    /// 文本向量化
    pub fn vectorize(&self, text: &str) -> Vec<f64> {
        let words = self.tokenize(text);
        let mut vector = vec![0.0; self.vocabulary.len()];

        for word in words {
            if let Some(&index) = self.vocabulary.get(&word) {
                vector[index] += 1.0;
            }
        }

        // 归一化
        let sum: f64 = vector.iter().sum();
        if sum > 0.0 {
            for val in &mut vector {
                *val /= sum;
            }
        }

        vector
    }
}

/// 情感分析器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SentimentAnalyzer {
    pub positive_words: Vec<String>,
    pub negative_words: Vec<String>,
    pub weights: HashMap<String, f64>,
}

impl SentimentAnalyzer {
    /// 创建新的情感分析器
    pub fn new() -> Self {
        let positive_words = vec![
            "good".to_string(),
            "great".to_string(),
            "excellent".to_string(),
            "amazing".to_string(),
            "wonderful".to_string(),
            "fantastic".to_string(),
            "awesome".to_string(),
            "brilliant".to_string(),
            "perfect".to_string(),
            "love".to_string(),
        ];

        let negative_words = vec![
            "bad".to_string(),
            "terrible".to_string(),
            "awful".to_string(),
            "horrible".to_string(),
            "disgusting".to_string(),
            "hate".to_string(),
            "worst".to_string(),
            "disappointing".to_string(),
            "ugly".to_string(),
            "stupid".to_string(),
        ];

        let mut weights = HashMap::new();
        for word in &positive_words {
            weights.insert(word.clone(), 1.0);
        }
        for word in &negative_words {
            weights.insert(word.clone(), -1.0);
        }

        Self {
            positive_words,
            negative_words,
            weights,
        }
    }

    /// 分析文本情感
    pub fn analyze(&self, text: &str) -> SentimentResult {
        let text_lower = text.to_lowercase();
        let words = text_lower
            .split_whitespace()
            .map(|s| s.trim_matches(|c: char| !c.is_alphanumeric()))
            .filter(|s| !s.is_empty())
            .collect::<Vec<_>>();

        let mut score = 0.0;
        let mut word_count = 0;

        for word in words {
            if let Some(&weight) = self.weights.get(word) {
                score += weight;
                word_count += 1;
            }
        }

        let sentiment = if score > 0.1 {
            Sentiment::Positive
        } else if score < -0.1 {
            Sentiment::Negative
        } else {
            Sentiment::Neutral
        };

        SentimentResult {
            sentiment,
            score: if word_count > 0 {
                score / word_count as f64
            } else {
                0.0
            },
            confidence: (score.abs() / word_count.max(1) as f64).min(1.0),
        }
    }
}

/// 情感类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Sentiment {
    Positive,
    Negative,
    Neutral,
}

/// 情感分析结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SentimentResult {
    pub sentiment: Sentiment,
    pub score: f64,
    pub confidence: f64,
}

/// 命名实体识别器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NamedEntityRecognizer {
    pub person_patterns: Vec<String>,
    pub location_patterns: Vec<String>,
    pub organization_patterns: Vec<String>,
}

impl NamedEntityRecognizer {
    /// 创建新的NER
    pub fn new() -> Self {
        Self {
            person_patterns: vec![
                "Mr.".to_string(),
                "Ms.".to_string(),
                "Dr.".to_string(),
                "Professor".to_string(),
                "President".to_string(),
            ],
            location_patterns: vec![
                "City".to_string(),
                "State".to_string(),
                "Country".to_string(),
                "Street".to_string(),
                "Avenue".to_string(),
                "Road".to_string(),
            ],
            organization_patterns: vec![
                "Inc.".to_string(),
                "Corp.".to_string(),
                "Ltd.".to_string(),
                "Company".to_string(),
                "University".to_string(),
                "Institute".to_string(),
            ],
        }
    }

    /// 识别命名实体
    pub fn recognize(&self, text: &str) -> Vec<NamedEntity> {
        let mut entities = Vec::new();
        let words = text.split_whitespace().collect::<Vec<_>>();

        for (i, word) in words.iter().enumerate() {
            // 检查人名
            if self
                .person_patterns
                .iter()
                .any(|pattern| word.contains(pattern))
            {
                entities.push(NamedEntity {
                    text: word.to_string(),
                    entity_type: EntityType::Person,
                    start: i,
                    end: i + 1,
                });
            }

            // 检查地名
            if self
                .location_patterns
                .iter()
                .any(|pattern| word.contains(pattern))
            {
                entities.push(NamedEntity {
                    text: word.to_string(),
                    entity_type: EntityType::Location,
                    start: i,
                    end: i + 1,
                });
            }

            // 检查机构名
            if self
                .organization_patterns
                .iter()
                .any(|pattern| word.contains(pattern))
            {
                entities.push(NamedEntity {
                    text: word.to_string(),
                    entity_type: EntityType::Organization,
                    start: i,
                    end: i + 1,
                });
            }
        }

        entities
    }
}

/// 实体类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum EntityType {
    Person,
    Location,
    Organization,
    Date,
    Money,
}

/// 命名实体
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NamedEntity {
    pub text: String,
    pub entity_type: EntityType,
    pub start: usize,
    pub end: usize,
}

/// 文本相似度计算器
pub struct TextSimilarity {
    pub method: SimilarityMethod,
}

/// 相似度计算方法
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SimilarityMethod {
    Cosine,
    Jaccard,
    Levenshtein,
}

impl TextSimilarity {
    /// 创建新的相似度计算器
    pub fn new(method: SimilarityMethod) -> Self {
        Self { method }
    }

    /// 计算文本相似度
    pub fn calculate(&self, text1: &str, text2: &str) -> f64 {
        match self.method {
            SimilarityMethod::Cosine => self.cosine_similarity(text1, text2),
            SimilarityMethod::Jaccard => self.jaccard_similarity(text1, text2),
            SimilarityMethod::Levenshtein => self.levenshtein_similarity(text1, text2),
        }
    }

    /// 余弦相似度
    fn cosine_similarity(&self, text1: &str, text2: &str) -> f64 {
        let text1_lower = text1.to_lowercase();
        let words1: std::collections::HashSet<_> = text1_lower.split_whitespace().collect();
        let text2_lower = text2.to_lowercase();
        let words2: std::collections::HashSet<_> = text2_lower.split_whitespace().collect();

        let intersection = words1.intersection(&words2).count();
        let union = words1.union(&words2).count();

        if union == 0 {
            0.0
        } else {
            intersection as f64 / union as f64
        }
    }

    /// Jaccard相似度
    fn jaccard_similarity(&self, text1: &str, text2: &str) -> f64 {
        let text1_lower = text1.to_lowercase();
        let words1: std::collections::HashSet<_> = text1_lower.split_whitespace().collect();
        let text2_lower = text2.to_lowercase();
        let words2: std::collections::HashSet<_> = text2_lower.split_whitespace().collect();

        let intersection = words1.intersection(&words2).count();
        let union = words1.union(&words2).count();

        if union == 0 {
            0.0
        } else {
            intersection as f64 / union as f64
        }
    }

    /// 编辑距离相似度
    fn levenshtein_similarity(&self, text1: &str, text2: &str) -> f64 {
        let distance = self.levenshtein_distance(text1, text2);
        let max_len = text1.len().max(text2.len());

        if max_len == 0 {
            1.0
        } else {
            1.0 - (distance as f64 / max_len as f64)
        }
    }

    /// 计算编辑距离
    fn levenshtein_distance(&self, s1: &str, s2: &str) -> usize {
        let chars1: Vec<char> = s1.chars().collect();
        let chars2: Vec<char> = s2.chars().collect();
        let len1 = chars1.len();
        let len2 = chars2.len();

        let mut matrix = vec![vec![0; len2 + 1]; len1 + 1];

        for i in 0..=len1 {
            matrix[i][0] = i;
        }
        for j in 0..=len2 {
            matrix[0][j] = j;
        }

        for i in 1..=len1 {
            for j in 1..=len2 {
                let cost = if chars1[i - 1] == chars2[j - 1] { 0 } else { 1 };
                matrix[i][j] = (matrix[i - 1][j] + 1)
                    .min(matrix[i][j - 1] + 1)
                    .min(matrix[i - 1][j - 1] + cost);
            }
        }

        matrix[len1][len2]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_text_preprocessor() {
        let mut preprocessor = TextPreprocessor::new(1000, 1);
        let texts = vec![
            "Hello world".to_string(),
            "Hello rust".to_string(),
            "World of rust".to_string(),
        ];

        preprocessor.build_vocabulary(&texts);
        assert!(!preprocessor.vocabulary.is_empty());

        let vector = preprocessor.vectorize("Hello world");
        assert_eq!(vector.len(), preprocessor.vocabulary.len());
    }

    #[test]
    fn test_sentiment_analyzer() {
        let analyzer = SentimentAnalyzer::new();

        let result = analyzer.analyze("This is a great movie!");
        assert_eq!(result.sentiment, Sentiment::Positive);

        let result = analyzer.analyze("This is a terrible movie!");
        assert_eq!(result.sentiment, Sentiment::Negative);

        let result = analyzer.analyze("This is a movie.");
        assert_eq!(result.sentiment, Sentiment::Neutral);
    }

    #[test]
    fn test_named_entity_recognizer() {
        let ner = NamedEntityRecognizer::new();
        let text = "Dr. Smith works at the University of California.";

        let entities = ner.recognize(text);
        assert!(!entities.is_empty());
    }

    #[test]
    fn test_text_similarity() {
        let similarity = TextSimilarity::new(SimilarityMethod::Cosine);

        let sim = similarity.calculate("Hello world", "Hello rust");
        assert!(sim >= 0.0 && sim <= 1.0);

        let sim = similarity.calculate("Hello world", "Hello world");
        assert_eq!(sim, 1.0);
    }
}
