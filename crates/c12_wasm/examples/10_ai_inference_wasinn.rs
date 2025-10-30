//! # AI 推理示例 - WASI-NN
//!
//! 本示例展示如何使用 WasmEdge WASI-NN 插件进行神经网络推理
//!
//! ## 支持的后端
//! - PyTorch
//! - TensorFlow Lite
//! - OpenVINO
//! - GGML (llama.cpp)
//!
//! ## 功能
//! - 图像分类
//! - 文本生成 (LLM)
//! - 自定义模型推理
//! - 批量处理
//!
//! ## 编译
//! ```bash
//! cargo build --example 10_ai_inference_wasinn --target wasm32-wasi --release
//! ```
//!
//! ## 运行
//! ```bash
//! # 使用 WasmEdge 运行（需要安装 WASI-NN 插件）
//! wasmedge --dir .:. \
//!   target/wasm32-wasi/release/examples/10_ai_inference_wasinn.wasm \
//!   model.onnx
//! ```
//!
//! ## 安装 WASI-NN 插件
//! ```bash
//! # Ubuntu/Debian
//! curl -sSf https://raw.githubusercontent.com/WasmEdge/WasmEdge/master/utils/install.sh | \
//!   bash -s -- --plugins wasi_nn-pytorch wasi_nn-ggml
//!
//! # 验证安装
//! wasmedge --version
//! ```

use std::fs;

/// WASI-NN 错误类型
#[derive(Debug)]
pub enum WasiNNError {
    ModelNotFound,
    LoadFailed(String),
    InferenceFailed(String),
    InvalidInput(String),
    BackendNotSupported(String),
}

impl std::fmt::Display for WasiNNError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ModelNotFound => write!(f, "Model file not found"),
            Self::LoadFailed(msg) => write!(f, "Failed to load model: {}", msg),
            Self::InferenceFailed(msg) => write!(f, "Inference failed: {}", msg),
            Self::InvalidInput(msg) => write!(f, "Invalid input: {}", msg),
            Self::BackendNotSupported(msg) => write!(f, "Backend not supported: {}", msg),
        }
    }
}

/// 推理后端类型
#[derive(Debug, Clone, Copy)]
pub enum InferenceBackend {
    /// PyTorch 后端
    PyTorch,
    /// TensorFlow Lite 后端
    TFLite,
    /// OpenVINO 后端
    OpenVINO,
    /// GGML 后端（用于 LLM）
    GGML,
}

impl InferenceBackend {
    #[allow(dead_code)]
    fn as_str(&self) -> &str {
        match self {
            Self::PyTorch => "pytorch",
            Self::TFLite => "tensorflowlite",
            Self::OpenVINO => "openvino",
            Self::GGML => "ggml",
        }
    }
}

/// 张量数据类型
#[derive(Debug, Clone, Copy)]
pub enum TensorType {
    F32,
    U8,
    I32,
    I64,
}

/// 图像分类器
pub struct ImageClassifier {
    model_path: String,
    backend: InferenceBackend,
    labels: Vec<String>,
}

impl ImageClassifier {
    pub fn new(model_path: String, backend: InferenceBackend) -> Result<Self, WasiNNError> {
        // 验证模型文件存在
        if !std::path::Path::new(&model_path).exists() {
            return Err(WasiNNError::ModelNotFound);
        }

        Ok(Self {
            model_path,
            backend,
            labels: Vec::new(),
        })
    }

    /// 加载标签文件
    pub fn load_labels(&mut self, labels_path: &str) -> Result<(), WasiNNError> {
        let content = fs::read_to_string(labels_path)
            .map_err(|e| WasiNNError::LoadFailed(format!("Failed to load labels: {}", e)))?;

        self.labels = content.lines().map(|s| s.to_string()).collect();
        println!("Loaded {} labels", self.labels.len());
        Ok(())
    }

    /// 预处理图像
    fn preprocess_image(&self, image_data: &[u8]) -> Result<Vec<f32>, WasiNNError> {
        // 这是一个简化版本
        // 实际应用中需要：
        // 1. 解码图像（JPEG/PNG）
        // 2. 调整大小
        // 3. 归一化
        // 4. 转换为模型期望的格式

        println!("Preprocessing image ({} bytes)", image_data.len());

        // 模拟预处理：转换为 f32 并归一化
        let processed: Vec<f32> = image_data
            .iter()
            .map(|&byte| (byte as f32) / 255.0)
            .collect();

        Ok(processed)
    }

    /// 执行推理
    pub fn classify(&self, image_data: &[u8]) -> Result<ClassificationResult, WasiNNError> {
        println!("=== Image Classification ===");
        println!("Backend: {:?}", self.backend);
        println!("Model: {}", self.model_path);

        // 预处理图像
        let input = self.preprocess_image(image_data)?;

        // 在实际实现中，这里会调用 WASI-NN API
        // 由于示例无法直接调用（需要实际的 WASI-NN 运行时），
        // 我们提供模拟实现

        println!("Input tensor shape: [{}, 224, 224, 3]", 1);
        println!("Running inference...");

        // 模拟推理结果
        let mock_result = self.mock_inference(&input);

        println!("Inference completed");

        Ok(mock_result)
    }

    /// 模拟推理（实际应使用 WASI-NN API）
    fn mock_inference(&self, _input: &[f32]) -> ClassificationResult {
        // 模拟输出概率
        vec![
            ("Cat".to_string(), 0.85),
            ("Dog".to_string(), 0.10),
            ("Bird".to_string(), 0.03),
            ("Fish".to_string(), 0.02),
        ]
    }

    /// 获取 Top-K 结果
    pub fn top_k(&self, mut results: ClassificationResult, k: usize) -> ClassificationResult {
        results.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        results.truncate(k);
        results
    }
}

/// 分类结果：(标签, 置信度)
pub type ClassificationResult = Vec<(String, f32)>;

/// LLM 文本生成器
pub struct LLMGenerator {
    model_path: String,
    max_tokens: usize,
}

impl LLMGenerator {
    pub fn new(model_path: String) -> Result<Self, WasiNNError> {
        if !std::path::Path::new(&model_path).exists() {
            return Err(WasiNNError::ModelNotFound);
        }

        Ok(Self {
            model_path,
            max_tokens: 256,
        })
    }

    /// 设置最大生成 token 数
    pub fn with_max_tokens(mut self, max_tokens: usize) -> Self {
        self.max_tokens = max_tokens;
        self
    }

    /// 生成文本
    pub fn generate(&self, prompt: &str) -> Result<String, WasiNNError> {
        println!("=== LLM Text Generation ===");
        println!("Model: {}", self.model_path);
        println!("Prompt: {}", prompt);
        println!("Max tokens: {}", self.max_tokens);

        // 实际实现中使用 WASI-NN GGML 后端
        // 这里提供模拟实现

        println!("Tokenizing prompt...");
        let _tokens = self.tokenize(prompt);

        println!("Generating text...");
        let generated = self.mock_generate(prompt);

        println!("Generation completed");
        Ok(generated)
    }

    /// 简单的分词器（模拟）
    fn tokenize(&self, text: &str) -> Vec<u32> {
        // 实际应使用模型的 tokenizer
        text.split_whitespace()
            .map(|word| word.len() as u32)
            .collect()
    }

    /// 模拟文本生成
    fn mock_generate(&self, prompt: &str) -> String {
        format!(
            "{} This is a simulated response from the language model. \
             In a real implementation, this would use WASI-NN with GGML backend \
             to generate text using models like LLaMA, GPT, or other LLMs.",
            prompt
        )
    }
}

/// 批量推理处理器
#[allow(dead_code)]
pub struct BatchInference {
    model_path: String,
    backend: InferenceBackend,
    batch_size: usize,
}

impl BatchInference {
    pub fn new(
        model_path: String,
        backend: InferenceBackend,
        batch_size: usize,
    ) -> Result<Self, WasiNNError> {
        if !std::path::Path::new(&model_path).exists() {
            return Err(WasiNNError::ModelNotFound);
        }

        Ok(Self {
            model_path,
            backend,
            batch_size,
        })
    }

    /// 批量处理多个输入
    pub fn process_batch(&self, inputs: Vec<Vec<f32>>) -> Result<Vec<Vec<f32>>, WasiNNError> {
        println!("=== Batch Inference ===");
        println!("Batch size: {}", self.batch_size);
        println!("Number of inputs: {}", inputs.len());

        let mut results = Vec::new();
        for chunk in inputs.chunks(self.batch_size) {
            println!("Processing batch of {} items", chunk.len());
            for _input in chunk {
                // 模拟推理
                let output = vec![0.1f32; 10]; // 模拟输出
                results.push(output);
            }
        }

        println!("Batch processing completed");
        Ok(results)
    }
}

/// 模型性能分析
pub struct ModelBenchmark {
    iterations: usize,
}

impl ModelBenchmark {
    pub fn new(iterations: usize) -> Self {
        Self { iterations }
    }

    /// 基准测试
    pub fn benchmark<F>(&self, name: &str, mut inference_fn: F)
    where
        F: FnMut() -> Result<(), WasiNNError>,
    {
        println!("\n=== Benchmarking: {} ===", name);
        println!("Iterations: {}", self.iterations);

        let start = std::time::Instant::now();

        for i in 0..self.iterations {
            if let Err(e) = inference_fn() {
                eprintln!("Iteration {} failed: {}", i, e);
                break;
            }
        }

        let duration = start.elapsed();
        let avg_ms = duration.as_millis() as f64 / self.iterations as f64;

        println!("Total time: {:?}", duration);
        println!("Average per iteration: {:.2} ms", avg_ms);
        println!("Throughput: {:.2} inferences/sec", 1000.0 / avg_ms);
    }
}

/// 实用工具函数
pub mod utils {
    use super::*;

    /// 打印分类结果
    pub fn print_classification_results(results: &ClassificationResult) {
        println!("\nClassification Results:");
        println!("{:-<50}", "");
        for (i, (label, confidence)) in results.iter().enumerate() {
            println!("{:2}. {:30} {:6.2}%", i + 1, label, confidence * 100.0);
        }
        println!("{:-<50}", "");
    }

    /// 打印张量形状
    pub fn print_tensor_info(name: &str, shape: &[usize], dtype: TensorType) {
        println!(
            "Tensor '{}': shape={:?}, dtype={:?}",
            name, shape, dtype
        );
    }
}

fn main() {
    println!("========================================");
    println!("  WasmEdge WASI-NN Inference Example");
    println!("  AI/ML in WebAssembly");
    println!("========================================\n");

    // 演示 1: 图像分类
    demo_image_classification();

    // 演示 2: LLM 文本生成
    demo_llm_generation();

    // 演示 3: 批量推理
    demo_batch_inference();

    // 演示 4: 性能基准测试
    demo_benchmarking();

    println!("\n========================================");
    println!("  All demonstrations completed!");
    println!("========================================");
}

fn demo_image_classification() {
    println!("\n### Demo 1: Image Classification ###\n");

    match ImageClassifier::new(
        "mobilenet_v2.onnx".to_string(),
        InferenceBackend::PyTorch,
    ) {
        Ok(classifier) => {
            // 模拟图像数据
            let mock_image = vec![128u8; 224 * 224 * 3];

            match classifier.classify(&mock_image) {
                Ok(results) => {
                    let top5 = classifier.top_k(results, 5);
                    utils::print_classification_results(&top5);
                }
                Err(e) => eprintln!("Classification failed: {}", e),
            }
        }
        Err(e) => eprintln!("Failed to create classifier: {}", e),
    }
}

fn demo_llm_generation() {
    println!("\n### Demo 2: LLM Text Generation ###\n");

    match LLMGenerator::new("llama-7b.ggml".to_string()) {
        Ok(generator) => {
            let prompts = vec![
                "The future of WebAssembly is",
                "Explain quantum computing in simple terms:",
                "Write a haiku about coding:",
            ];

            for prompt in prompts {
                match generator.generate(prompt) {
                    Ok(text) => {
                        println!("\nPrompt: {}", prompt);
                        println!("Generated: {}\n", text);
                    }
                    Err(e) => eprintln!("Generation failed: {}", e),
                }
            }
        }
        Err(e) => eprintln!("Failed to create generator: {}", e),
    }
}

fn demo_batch_inference() {
    println!("\n### Demo 3: Batch Inference ###\n");

    match BatchInference::new(
        "model.onnx".to_string(),
        InferenceBackend::PyTorch,
        32, // batch size
    ) {
        Ok(processor) => {
            // 创建模拟输入
            let inputs: Vec<Vec<f32>> = (0..100).map(|_| vec![0.5f32; 224 * 224 * 3]).collect();

            match processor.process_batch(inputs) {
                Ok(outputs) => {
                    println!("Successfully processed {} batches", outputs.len());
                }
                Err(e) => eprintln!("Batch processing failed: {}", e),
            }
        }
        Err(e) => eprintln!("Failed to create batch processor: {}", e),
    }
}

fn demo_benchmarking() {
    println!("\n### Demo 4: Performance Benchmarking ###\n");

    let benchmark = ModelBenchmark::new(100);

    benchmark.benchmark("Image Classification", || {
        // 模拟推理
        let _mock_result = vec![0.1f32; 1000];
        std::thread::sleep(std::time::Duration::from_micros(100));
        Ok(())
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tensor_types() {
        let types = vec![
            TensorType::F32,
            TensorType::U8,
            TensorType::I32,
            TensorType::I64,
        ];
        assert_eq!(types.len(), 4);
    }

    #[test]
    fn test_backend_names() {
        assert_eq!(InferenceBackend::PyTorch.as_str(), "pytorch");
        assert_eq!(InferenceBackend::TFLite.as_str(), "tensorflowlite");
        assert_eq!(InferenceBackend::OpenVINO.as_str(), "openvino");
        assert_eq!(InferenceBackend::GGML.as_str(), "ggml");
    }

    #[test]
    fn test_error_display() {
        let error = WasiNNError::ModelNotFound;
        assert_eq!(error.to_string(), "Model file not found");
    }
}

