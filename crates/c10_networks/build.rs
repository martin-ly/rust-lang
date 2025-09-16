fn main() {
	let proto_dir = "proto";
	if std::path::Path::new(proto_dir).exists() {
		let protoc_path = protoc_bin_vendored::protoc_bin_path().expect("vendored protoc");
		unsafe { std::env::set_var("PROTOC", protoc_path); }
		
		// 使用 tonic-prost-build 编译 protobuf 文件，生成 gRPC 客户端和服务端代码
		tonic_prost_build::configure()
			.build_server(true)
			.build_client(true)
			.compile_protos(&["proto/hello.proto"], &["proto"])
			.expect("failed to compile protos");
	}
}
