fn main() {
    println!("cargo:rerun-if-changed=proto/hello.proto");

    let proto_dir = "proto";
    if std::path::Path::new(proto_dir).exists() {
        println!("cargo:warning=Proto directory exists, compiling protobuf files");

        // 使用 vendored protoc，避免本地未安装导致失败
        unsafe {
            if let Ok(protoc_path) = protoc_bin_vendored::protoc_bin_path() {
                std::env::set_var("PROTOC", protoc_path);
            }
        }
        
        // 使用 tonic-prost-build 生成带有 gRPC 客户端/服务端的代码
        tonic_prost_build::configure()
            .build_server(true)
            .build_client(true)
            .compile_protos(&["proto/hello.proto"], &["proto"]) // (files, includes)
            .expect("failed to compile protos with tonic-prost-build");

        println!("cargo:warning=Protobuf compilation completed");
    } else {
        println!("cargo:warning=Proto directory does not exist");
    }
}
