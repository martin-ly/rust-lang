fn main() {
    let proto_dir = "proto";
    if std::path::Path::new(proto_dir).exists() {
        let protoc_path = protoc_bin_vendored::protoc_bin_path().expect("vendored protoc");
        unsafe {
            std::env::set_var("PROTOC", protoc_path);
        }

        // 使用 prost-build 编译 protobuf 文件
        prost_build::compile_protos(&["proto/user_service.proto"], &["proto"])
            .expect("failed to compile protos");
    }
}
