use std::env;
use std::fs;
use std::path::{Path, PathBuf};

fn main() {
    // 1. 读取构建信息文件，并在其变更时重新运行 build.rs
    let info_path = Path::new("build-info.json");
    println!("cargo:rerun-if-changed={}", info_path.display());

    // 2. 从 build-info.json 中提取字段，生成到 OUT_DIR 的 Rust 源码
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR not set"));
    let info: serde_json::Value = serde_json::from_str(
        &fs::read_to_string(info_path).expect("failed to read build-info.json"),
    )
    .expect("failed to parse build-info.json");

    let project = info["project"].as_str().unwrap_or("unknown");
    let maintainer = info["maintainer"].as_str().unwrap_or("unknown");
    let license = info["license"].as_str().unwrap_or("unknown");

    let generated = format!(
        "// 由 build.rs 自动生成，请勿手动编辑。\n\
         pub const PROJECT_NAME: &str = \"{project}\";\n\
         pub const MAINTAINER: &str = \"{maintainer}\";\n\
         pub const LICENSE: &str = \"{license}\";\n"
    );
    fs::write(out_dir.join("build_info.rs"), generated).expect("failed to write build_info.rs");

    // 3. 使用 cc crate 编译 native/math.c
    println!("cargo:rerun-if-changed=native/math.c");
    cc::Build::new()
        .file("native/math.c")
        .compile("mymath");
}
