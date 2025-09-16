fn main() {
    println!("cargo:rerun-if-changed=proto/hello.proto");
    
    let proto_dir = "proto";
    if std::path::Path::new(proto_dir).exists() {
        println!("cargo:warning=Proto directory exists, compiling protobuf files");
        
        let protoc_path = protoc_bin_vendored::protoc_bin_path().expect("vendored protoc");
        unsafe {
            std::env::set_var("PROTOC", protoc_path);
        }

        // 使用 prost-build 编译 protobuf 文件
        let mut config = prost_build::Config::new();
        config.compile_protos(&["proto/hello.proto"], &["proto"])
            .expect("failed to compile protos");
            
        println!("cargo:warning=Protobuf compilation completed");
    } else {
        println!("cargo:warning=Proto directory does not exist");
    }
}
