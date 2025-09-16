fn main() {
    // 测试 tonic-build 的可用函数
    println!("Testing tonic-build functions...");
    
    // 尝试使用不同的 API
    if let Ok(_) = tonic_build::compile_protos(&["proto/user_service.proto"], &["proto"]) {
        println!("compile_protos works!");
    } else {
        println!("compile_protos failed");
    }
}
