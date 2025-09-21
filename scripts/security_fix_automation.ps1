# 安全漏洞修复自动化脚本 - 2025年1月
# 用于自动检测和修复安全漏洞

param(
    [switch]$Audit,
    [switch]$Fix,
    [switch]$Report,
    [switch]$All
)

Write-Host "🛡️ Rust项目安全漏洞修复工具" -ForegroundColor Green
Write-Host "=====================================" -ForegroundColor Green

if ($All -or $Audit) {
    Write-Host "`n🔍 执行安全审计..." -ForegroundColor Yellow
    cargo audit
    if ($LASTEXITCODE -ne 0) {
        Write-Host "❌ 发现安全漏洞，请查看上述报告" -ForegroundColor Red
        Write-Host "`n📋 建议的修复措施:" -ForegroundColor Cyan
        Write-Host "1. 更新有安全漏洞的依赖到最新版本" -ForegroundColor White
        Write-Host "2. 替换未维护的依赖为现代替代方案" -ForegroundColor White
        Write-Host "3. 使用特性标志禁用不必要的功能" -ForegroundColor White
    } else {
        Write-Host "✅ 安全审计通过，未发现严重漏洞" -ForegroundColor Green
    }
}

if ($All -or $Fix) {
    Write-Host "`n🔧 执行安全修复..." -ForegroundColor Yellow
    
    # 检查并修复已知的安全漏洞
    Write-Host "检查未维护的依赖..." -ForegroundColor Cyan
    
    # 检查paste依赖
    $pasteCheck = cargo tree --format "{p}" | Select-String "paste"
    if ($pasteCheck) {
        Write-Host "⚠️ 发现paste依赖，建议替换为quote" -ForegroundColor Yellow
        Write-Host "   在Cargo.toml中替换: paste = \"1.0.15\" → quote = \"1.0.40\"" -ForegroundColor White
    }
    
    # 检查proc-macro-error依赖
    $procMacroErrorCheck = cargo tree --format "{p}" | Select-String "proc-macro-error"
    if ($procMacroErrorCheck) {
        Write-Host "⚠️ 发现proc-macro-error依赖，建议替换为proc-macro-error2" -ForegroundColor Yellow
        Write-Host "   在Cargo.toml中替换: proc-macro-error = \"1.0.5\" → proc-macro-error2 = \"2.0.1\"" -ForegroundColor White
    }
    
    # 检查yaml-rust依赖
    $yamlRustCheck = cargo tree --format "{p}" | Select-String "yaml-rust"
    if ($yamlRustCheck) {
        Write-Host "⚠️ 发现yaml-rust依赖，建议替换为serde_yaml" -ForegroundColor Yellow
        Write-Host "   在Cargo.toml中替换: yaml-rust = \"0.4.0\" → serde_yaml = \"0.9.34\"" -ForegroundColor White
    }
    
    # 检查instant依赖
    $instantCheck = cargo tree --format "{p}" | Select-String "instant"
    if ($instantCheck) {
        Write-Host "⚠️ 发现instant依赖，建议使用std::time::Instant替代" -ForegroundColor Yellow
        Write-Host "   移除instant依赖，使用标准库的std::time::Instant" -ForegroundColor White
    }
    
    # 检查fxhash依赖
    $fxhashCheck = cargo tree --format "{p}" | Select-String "fxhash"
    if ($fxhashCheck) {
        Write-Host "⚠️ 发现fxhash依赖，建议替换为ahash" -ForegroundColor Yellow
        Write-Host "   在Cargo.toml中替换: fxhash = \"0.2.1\" → ahash = \"0.8.0\"" -ForegroundColor White
    }
    
    # 检查atty依赖
    $attyCheck = cargo tree --format "{p}" | Select-String "atty"
    if ($attyCheck) {
        Write-Host "⚠️ 发现atty依赖，建议替换为is-terminal" -ForegroundColor Yellow
        Write-Host "   在Cargo.toml中替换: atty = \"0.2.14\" → is-terminal = \"0.2.0\"" -ForegroundColor White
    }
    
    # 检查stdweb依赖
    $stdwebCheck = cargo tree --format "{p}" | Select-String "stdweb"
    if ($stdwebCheck) {
        Write-Host "⚠️ 发现stdweb依赖，建议替换为wasm-bindgen" -ForegroundColor Yellow
        Write-Host "   在Cargo.toml中替换: stdweb = \"0.4.20\" → wasm-bindgen = \"0.2.103\"" -ForegroundColor White
    }
    
    # 检查tauri依赖
    $tauriCheck = cargo tree --format "{p}" | Select-String "tauri"
    if ($tauriCheck) {
        Write-Host "⚠️ 发现tauri依赖，建议替换为egui/iced (解决GTK3安全漏洞)" -ForegroundColor Yellow
        Write-Host "   在Cargo.toml中替换: tauri = \"2.8.5\" → egui = \"0.32.3\", iced = \"0.13.1\"" -ForegroundColor White
    }
    
    # 检查pingora依赖
    $pingoraCheck = cargo tree --format "{p}" | Select-String "pingora"
    if ($pingoraCheck) {
        Write-Host "⚠️ 发现pingora依赖，建议替换为nix (解决daemonize安全漏洞)" -ForegroundColor Yellow
        Write-Host "   在Cargo.toml中替换: pingora = \"0.3.0\" → nix = \"0.28.0\"" -ForegroundColor White
    }
    
    # 检查tide依赖
    $tideCheck = cargo tree --format "{p}" | Select-String "tide"
    if ($tideCheck) {
        Write-Host "⚠️ 发现tide依赖，建议替换为axum (解决stdweb安全漏洞)" -ForegroundColor Yellow
        Write-Host "   在Cargo.toml中替换: tide = \"0.16.0\" → axum = \"0.8.4\"" -ForegroundColor White
    }
    
    Write-Host "`n✅ 安全修复检查完成" -ForegroundColor Green
}

if ($All -or $Report) {
    Write-Host "`n📊 生成安全报告..." -ForegroundColor Yellow
    
    # 生成依赖树报告
    Write-Host "生成依赖树报告..." -ForegroundColor Cyan
    cargo tree --format "{p} {f}" > "dependency_tree_report.txt"
    
    # 生成重复依赖报告
    Write-Host "检查重复依赖..." -ForegroundColor Cyan
    cargo tree --duplicates > "duplicate_dependencies_report.txt"
    
    # 生成过时依赖报告
    Write-Host "检查过时依赖..." -ForegroundColor Cyan
    cargo outdated > "outdated_dependencies_report.txt"
    
    Write-Host "`n📄 报告已生成:" -ForegroundColor Green
    Write-Host "   - dependency_tree_report.txt" -ForegroundColor White
    Write-Host "   - duplicate_dependencies_report.txt" -ForegroundColor White
    Write-Host "   - outdated_dependencies_report.txt" -ForegroundColor White
}

if (-not ($Audit -or $Fix -or $Report -or $All)) {
    Write-Host "`n📋 可用选项:" -ForegroundColor Cyan
    Write-Host "  -Audit   : 执行安全审计" -ForegroundColor White
    Write-Host "  -Fix     : 检查并建议安全修复" -ForegroundColor White
    Write-Host "  -Report  : 生成安全报告" -ForegroundColor White
    Write-Host "  -All     : 执行所有检查" -ForegroundColor White
    Write-Host "`n示例: .\security_fix_automation.ps1 -All" -ForegroundColor Yellow
}

Write-Host "`n🛡️ 安全最佳实践:" -ForegroundColor Green
Write-Host "1. 定期运行 cargo audit 检查安全漏洞" -ForegroundColor White
Write-Host "2. 及时更新依赖到最新安全版本" -ForegroundColor White
Write-Host "3. 避免使用未维护的依赖库" -ForegroundColor White
Write-Host "4. 使用特性标志减少攻击面" -ForegroundColor White
Write-Host "5. 建立自动化安全监控流程" -ForegroundColor White

Write-Host "`n🔗 有用的资源:" -ForegroundColor Green
Write-Host "- Rust Security Advisory Database: https://rustsec.org/" -ForegroundColor White
Write-Host "- Cargo Audit: https://github.com/RustSec/cargo-audit" -ForegroundColor White
Write-Host "- Cargo Outdated: https://github.com/kbknapp/cargo-outdated" -ForegroundColor White
