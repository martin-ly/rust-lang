use std::process::Command;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 检查是否有protoc编译器
    let protoc_available = check_protoc_availability();
    
    if !protoc_available {
        println!("cargo:warning=protoc not found, skipping proto compilation");
        println!("cargo:warning=To enable gRPC features, please install protoc:");
        println!("cargo:warning=  Windows: Run scripts/install_protoc.ps1");
        println!("cargo:warning=  Linux/macOS: Run scripts/install_protoc.sh");
        return Ok(());
    }
    
    println!("cargo:info=Found protoc, compiling proto files...");
    
    tonic_build::configure()
        .build_server(true)
        .build_client(true)
        .compile_protos(&["proto/user_service.proto"], &["proto"])?;
    
    println!("cargo:info=Proto compilation completed successfully");
    Ok(())
}

fn check_protoc_availability() -> bool {
    // 首先检查环境变量
    if std::env::var("PROTOC").is_ok() {
        return true;
    }
    
    // 检查PATH中的protoc
    match Command::new("protoc").arg("--version").output() {
        Ok(output) => {
            if output.status.success() {
                let version = String::from_utf8_lossy(&output.stdout);
                println!("cargo:info=Found protoc: {}", version.trim());
                return true;
            }
        }
        Err(_) => {
            // protoc not found in PATH
        }
    }
    
    false
}
