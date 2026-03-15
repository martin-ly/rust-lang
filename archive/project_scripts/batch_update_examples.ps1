# 批量更新根级示例

$section = @"

// Rust 1.94 特性示例
fn rust_194_features_demo() {
    println!("\n🆕 Rust 1.94 特性演示");
    
    // array_windows
    let data = [1, 2, 3, 4, 5];
    for window in data.array_windows::<2>() {
        println!("  Window: {:?}", window);
    }
    
    // ControlFlow
    use std::ops::ControlFlow;
    let result = [1, 2, 3].iter().try_for_each(|&n| {
        if n > 2 { ControlFlow::Break(n) }
        else { ControlFlow::Continue(()) }
    });
    println!("  ControlFlow: {:?}", result.break_value());
}
"@

$files = @(
    "comprehensive_integration_example.rs",
    "module_complete_examples.rs",
    "real_world_applications.rs"
)

foreach ($file in $files) {
    $path = "examples/$file"
    if (Test-Path $path) {
        $content = Get-Content $path -Raw
        
        if (-not ($content -match "Rust 1\.94")) {
            # 在文件末尾添加
            $content = $content + "`n$section"
            Set-Content $path $content -NoNewline
            Write-Host "✅ 已更新: $file"
        } else {
            Write-Host "⏭️  跳过: $file"
        }
    }
}

Write-Host "`n示例文件更新完成!"
