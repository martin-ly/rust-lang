fn main() {
	let proto_dir = "proto";
	if std::path::Path::new(proto_dir).exists() {
		let protoc_path = protoc_bin_vendored::protoc_bin_path().expect("vendored protoc");
		unsafe { std::env::set_var("PROTOC", protoc_path); }
		tonic_build::configure()
			.compile_well_known_types(true)
			.compile_protos(&["proto/hello.proto"], &[proto_dir])
			.expect("failed to compile protos");
	}
}
