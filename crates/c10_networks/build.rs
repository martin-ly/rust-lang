use std::path::Path;

fn main() {
    // 优化1: 只有当 proto 文件变化时才重新运行构建脚本
    println!("cargo:rerun-if-changed=proto/hello.proto");
    
    // 优化2: 告诉 Cargo 这个构建脚本不依赖于其他文件
    println!("cargo:rerun-if-env-changed=PROTOC");
    println!("cargo:rerun-if-env-changed=PROTOC_INCLUDE");

    let proto_dir = "proto";
    let proto_file = "proto/hello.proto";
    
    // 如果 proto 文件不存在，跳过编译
    if !Path::new(proto_file).exists() {
        println!("cargo:warning=Proto file does not exist: {}", proto_file);
        return;
    }

    // 优化3: 检查生成的文件是否比 proto 文件新，如果是则跳过编译
    let out_dir = std::env::var("OUT_DIR").expect("OUT_DIR not set");
    let generated_file = Path::new(&out_dir).join("hello.rs");
    
    if let (Ok(proto_meta), Ok(gen_meta)) = (
        std::fs::metadata(proto_file),
        std::fs::metadata(&generated_file)
    ) {
        if let (Ok(proto_time), Ok(gen_time)) = (
            proto_meta.modified(),
            gen_meta.modified()
        ) {
            if gen_time > proto_time {
                println!("cargo:warning=Generated code is up to date, skipping protobuf compilation");
                return;
            }
        }
    }

    if Path::new(proto_dir).exists() {
        // 使用 vendored protoc，避免本地未安装导致失败
        unsafe {
            if let Ok(protoc_path) = protoc_bin_vendored::protoc_bin_path() {
                std::env::set_var("PROTOC", protoc_path);
            }
        }

        // 优化4: 配置 prost-build 以提高性能
        let mut config = tonic_prost_build::configure();
        
        // 优化5: 使用 bytes 类型减少拷贝
        config = config.bytes(".");
        
        // 编译 proto 文件
        config
            .build_server(true)
            .build_client(true)
            .compile_protos(&[proto_file], &[proto_dir])
            .expect("failed to compile protobuf files with tonic-prost-build");
            
        println!("cargo:warning=Protobuf compilation completed successfully");
    } else {
        println!("cargo:warning=Proto directory does not exist: {}", proto_dir);
    }
}
