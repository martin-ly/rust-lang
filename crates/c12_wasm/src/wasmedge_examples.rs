//! # WasmEdge 和新技术示例代码
//!
//! 本模块展示了如何使用 WasmEdge 和最新的 WASM 技术

/// WasmEdge 高级特性示例
pub mod wasmedge_advanced {
    use std::fs;
    use std::io::{Read, Write};
    use std::net::TcpListener;

    /// 使用 WasmEdge 运行 HTTP 服务器
    ///
    /// # 特性
    /// - 快速启动（AOT 编译）
    /// - 低内存占用
    /// - 高并发支持
    ///
    /// # 使用方式
    /// ```bash
    /// wasmedge --allow-net --enable-threads server.wasm
    /// ```
    pub fn run_http_server() -> Result<(), Box<dyn std::error::Error>> {
        let listener = TcpListener::bind("127.0.0.1:8080")?;
        println!("Server listening on http://127.0.0.1:8080");

        for stream in listener.incoming() {
            match stream {
                Ok(mut stream) => {
                    let mut buffer = [0; 1024];
                    stream.read(&mut buffer)?;

                    let response = b"HTTP/1.1 200 OK\r\n\r\nHello from WasmEdge!";
                    stream.write(response)?;
                    stream.flush()?;
                }
                Err(e) => {
                    eprintln!("Error: {}", e);
                }
            }
        }

        Ok(())
    }

    /// 高性能文件处理（利用 WasmEdge 零拷贝特性）
    ///
    /// # 性能说明
    /// WasmEdge 会自动优化文件访问，减少内存复制
    pub fn process_large_file(path: &str) -> Result<usize, Box<dyn std::error::Error>> {
        let content = fs::read_to_string(path)?;
        let processed = content
            .lines()
            .filter(|line| !line.is_empty())
            .count();
        Ok(processed)
    }

    /// 内存管理示例
    ///
    /// # 性能优化
    /// - 预分配容量
    /// - 重用缓冲区
    pub fn efficient_data_processing(data: &[u8]) -> Vec<u8> {
        let mut result = Vec::with_capacity(data.len());
        result.extend_from_slice(data);
        // 处理数据...
        result
    }
}

/// WASI-NN AI 推理示例
pub mod wasi_nn_examples {
    /// 图像分类示例
    ///
    /// # 注意
    /// 实际实现需要使用 WASI-NN bindings
    ///
    /// # 使用 WasmEdge 运行
    /// ```bash
    /// wasmedge --enable-wasi-nn --enable-wasi-nn-tensorflow app.wasm
    /// ```
    #[allow(dead_code)]
    pub struct ImageClassifier {
        // 模型数据
        model_data: Vec<u8>,
    }

    impl ImageClassifier {
        pub fn new(model_path: &str) -> Result<Self, Box<dyn std::error::Error>> {
            let model_data = std::fs::read(model_path)?;
            Ok(Self { model_data })
        }

        /// 运行图像分类
        ///
        /// # 参数
        /// - `image_data`: 图像数据（JPEG/PNG 格式）
        ///
        /// # 返回值
        /// 返回分类结果（类别索引和置信度）
        pub fn classify(&self, _image_data: &[u8]) -> Result<Vec<f32>, String> {
            // 实际实现需要使用 WASI-NN API
            // 这里只是示例结构

            // 1. 加载模型（通过 WASI-NN）
            // let model = wasi_nn::load_model(&self.model_data)?;

            // 2. 设置输入
            // wasi_nn::set_input(model, &image_data)?;

            // 3. 运行推理
            // let outputs = wasi_nn::compute(model)?;

            // 4. 获取结果
            // Ok(outputs)

            Ok(vec![0.0]) // 占位符
        }
    }

    /// 文本处理示例（使用 AI 模型）
    #[allow(dead_code)]
    pub struct TextProcessor {
        model_data: Vec<u8>,
    }

    impl TextProcessor {
        pub fn new(model_path: &str) -> Result<Self, Box<dyn std::error::Error>> {
            let model_data = std::fs::read(model_path)?;
            Ok(Self { model_data })
        }

        /// 处理文本
        pub fn process(&self, text: &str) -> Result<String, String> {
            // 使用 AI 模型处理文本
            // 实际实现需要使用 WASI-NN
            Ok(text.to_uppercase()) // 占位符
        }
    }
}

/// WASI-Crypto 示例
pub mod wasi_crypto_examples {
    /// 数据加密示例
    ///
    /// # 使用 WasmEdge 运行
    /// ```bash
    /// wasmedge --enable-wasi-crypto app.wasm
    /// ```
    pub fn encrypt_data(data: &[u8], _key: &[u8]) -> Result<Vec<u8>, String> {
        // 实际实现需要使用 WASI-Crypto API
        // 这里只是示例结构

        // 使用 AES-256-GCM 加密
        // let encrypted = wasi_crypto::symmetric::encrypt(
        //     data,
        //     key,
        //     wasi_crypto::symmetric::Algorithm::Aes256Gcm
        // )?;

        Ok(data.to_vec()) // 占位符
    }

    /// 数据哈希示例
    pub fn hash_data(_data: &[u8]) -> Vec<u8> {
        // 使用 SHA-256 哈希
        // 实际实现需要使用 WASI-Crypto
        // wasi_crypto::hash::hash(data, wasi_crypto::hash::Algorithm::Sha256)

        vec![0; 32] // 占位符（SHA-256 输出 32 字节）
    }

    /// 数字签名示例
    pub fn sign_data(_data: &[u8], _private_key: &[u8]) -> Result<Vec<u8>, String> {
        // 使用 ECDSA 签名
        // 实际实现需要使用 WASI-Crypto
        Ok(vec![0; 64]) // 占位符
    }

    /// 验证签名
    pub fn verify_signature(
        _data: &[u8],
        _signature: &[u8],
        _public_key: &[u8],
    ) -> Result<bool, String> {
        // 验证 ECDSA 签名
        // 实际实现需要使用 WASI-Crypto
        Ok(true) // 占位符
    }
}

/// 多线程 WASM 示例
pub mod threading_examples {
    use std::sync::{Arc, Mutex};
    use std::thread;

    /// 并行处理数据
    ///
    /// # 使用 WasmEdge 运行
    /// ```bash
    /// wasmedge --enable-threads app.wasm
    /// ```
    pub fn parallel_process(data: &[i32], num_threads: usize) -> Vec<i32> {
        let chunk_size = data.len() / num_threads;
        let data = Arc::new(data.to_vec());
        let results = Arc::new(Mutex::new(Vec::new()));

        let handles: Vec<_> = (0..num_threads)
            .map(|i| {
                let data = Arc::clone(&data);
                let results = Arc::clone(&results);
                thread::spawn(move || {
                    let start = i * chunk_size;
                    let end = if i == num_threads - 1 {
                        data.len()
                    } else {
                        (i + 1) * chunk_size
                    };

                    let chunk: Vec<i32> = data[start..end]
                        .iter()
                        .map(|&x| x * 2)
                        .collect();

                    results.lock().unwrap().extend(chunk);
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        Arc::try_unwrap(results)
            .unwrap()
            .into_inner()
            .unwrap()
    }

    /// 线程池示例
    #[allow(dead_code)]
    pub struct ThreadPool {
        workers: Vec<thread::JoinHandle<()>>,
        sender: Option<std::sync::mpsc::Sender<Job>>,
    }

    type Job = Box<dyn FnOnce() + Send + 'static>;

    impl ThreadPool {
        pub fn new(size: usize) -> Self {
            let (sender, receiver) = std::sync::mpsc::channel();
            let receiver = Arc::new(Mutex::new(receiver));

            let workers = (0..size)
                .map(|_| {
                    let receiver = Arc::clone(&receiver);
                    thread::spawn(move || loop {
                        let job: Job = receiver.lock().unwrap().recv().unwrap();
                        job();
                    })
                })
                .collect();

            Self {
                workers,
                sender: Some(sender),
            }
        }

        pub fn execute<F>(&self, f: F)
        where
            F: FnOnce() + Send + 'static,
        {
            let job = Box::new(f);
            self.sender.as_ref().unwrap().send(job).unwrap();
        }
    }
}

/// WasmEdge 性能优化示例
pub mod performance_examples {
    use std::cell::RefCell;

    thread_local! {
        // 线程局部存储（优化内存分配）
        static BUFFER: RefCell<Vec<u8>> = RefCell::new(Vec::new());
    }

    /// 重用缓冲区的数据处理
    ///
    /// # 性能说明
    /// 通过重用线程局部缓冲区，避免频繁分配内存
    pub fn process_with_reuse(data: &[u8]) -> Vec<u8> {
        BUFFER.with(|buf| {
            let mut buffer = buf.borrow_mut();
            buffer.clear();

            if buffer.capacity() < data.len() {
                buffer.reserve(data.len());
            }

            buffer.extend_from_slice(data);
            buffer.clone()
        })
    }

    /// 批量处理（减少函数调用开销）
    pub fn batch_process(items: &[i32]) -> Vec<i32> {
        items.iter().map(|&x| x * 2).collect()
    }
}

/// 云原生应用示例
pub mod cloud_native_examples {
    /// 边缘计算函数
    ///
    /// # 特性
    /// - 快速启动
    /// - 低内存占用
    /// - 高并发
    pub fn edge_function(request: &[u8]) -> Vec<u8> {
        // 快速处理请求
        let response = format!(
            "HTTP/1.1 200 OK\r\nContent-Length: {}\r\n\r\n{}",
            request.len(),
            "Processed by WasmEdge"
        );
        response.into_bytes()
    }

    /// 微服务示例
    pub struct Microservice {
        name: String,
    }

    impl Microservice {
        pub fn new(name: String) -> Self {
            Self { name }
        }

        pub fn handle_request(&self, request: &str) -> String {
            format!("Service: {} handled: {}", self.name, request)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_process() {
        let data = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let result = threading_examples::parallel_process(&data, 2);
        assert_eq!(result.len(), data.len());
    }

    #[test]
    fn test_process_with_reuse() {
        let data = b"test data";
        let result = performance_examples::process_with_reuse(data);
        assert_eq!(result, data);
    }
}
