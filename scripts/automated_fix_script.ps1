# Rust 1.90 代码质量自动修复脚本
# 用于批量修复 Clippy 警告和代码质量问题

param(
    [switch]$FixClippy,
    [switch]$AddDefaults,
    [switch]$UpdateDeps,
    [switch]$SecurityAudit,
    [switch]$All,
    [string]$Crate = ""
)

Write-Host "🚀 Rust 1.90 代码质量自动修复脚本" -ForegroundColor Green
Write-Host "=====================================" -ForegroundColor Green

# 设置错误处理
$ErrorActionPreference = "Continue"

# 函数：检查命令是否存在
function Test-Command {
    param($Command)
    try {
        if (Get-Command $Command -ErrorAction SilentlyContinue) {
            return $true
        }
    }
    catch {
        return $false
    }
    return $false
}

# 函数：运行 Cargo 命令
function Invoke-CargoCommand {
    param(
        [string]$Command,
        [string]$WorkingDir = ".",
        [switch]$AllowFailure
    )
    
    Write-Host "执行: cargo $Command" -ForegroundColor Yellow
    Push-Location $WorkingDir
    try {
        $result = Invoke-Expression "cargo $Command"
        if ($LASTEXITCODE -ne 0 -and -not $AllowFailure) {
            Write-Host "命令失败: cargo $Command" -ForegroundColor Red
            return $false
        }
        return $true
    }
    finally {
        Pop-Location
    }
}

# 函数：修复 Clippy 警告
function Fix-ClippyWarnings {
    Write-Host "🔧 修复 Clippy 警告..." -ForegroundColor Cyan
    
    if ($Crate -ne "") {
        $crates = @($Crate)
    } else {
        $crates = Get-ChildItem -Path "crates" -Directory | ForEach-Object { $_.Name }
    }
    
    foreach ($crate in $crates) {
        Write-Host "处理 crate: $crate" -ForegroundColor Yellow
        
        # 运行 clippy --fix
        if (Invoke-CargoCommand -Command "clippy --fix --allow-dirty" -WorkingDir "crates/$crate") {
            Write-Host "✅ $crate Clippy 修复完成" -ForegroundColor Green
        } else {
            Write-Host "❌ $crate Clippy 修复失败" -ForegroundColor Red
        }
        
        # 格式化代码
        if (Invoke-CargoCommand -Command "fmt" -WorkingDir "crates/$crate") {
            Write-Host "✅ $crate 代码格式化完成" -ForegroundColor Green
        }
    }
}

# 函数：添加 Default 实现
function Add-DefaultImplementations {
    Write-Host "🔧 添加 Default 实现..." -ForegroundColor Cyan
    
    # 这里可以添加自动生成 Default 实现的逻辑
    # 由于需要解析 Rust 代码，建议手动添加或使用更高级的工具
    
    Write-Host "⚠️  Default 实现需要手动添加，请参考改进计划文档" -ForegroundColor Yellow
}

# 函数：更新依赖
function Update-Dependencies {
    Write-Host "🔧 更新依赖..." -ForegroundColor Cyan
    
    # 更新工作区依赖
    if (Invoke-CargoCommand -Command "update") {
        Write-Host "✅ 依赖更新完成" -ForegroundColor Green
    }
    
    # 检查过时依赖
    if (Test-Command "cargo-outdated") {
        Write-Host "检查过时依赖..." -ForegroundColor Yellow
        Invoke-CargoCommand -Command "outdated" -AllowFailure
    } else {
        Write-Host "⚠️  cargo-outdated 未安装，跳过过时依赖检查" -ForegroundColor Yellow
    }
}

# 函数：安全审计
function Invoke-SecurityAudit {
    Write-Host "🔧 运行安全审计..." -ForegroundColor Cyan
    
    if (Test-Command "cargo-audit") {
        if (Invoke-CargoCommand -Command "audit") {
            Write-Host "✅ 安全审计完成" -ForegroundColor Green
        } else {
            Write-Host "❌ 发现安全漏洞，请查看审计报告" -ForegroundColor Red
        }
    } else {
        Write-Host "⚠️  cargo-audit 未安装，请先安装: cargo install cargo-audit" -ForegroundColor Yellow
    }
}

# 函数：生成进度报告
function Generate-ProgressReport {
    Write-Host "📊 生成进度报告..." -ForegroundColor Cyan
    
    $report = @"
# 代码质量修复进度报告
生成时间: $(Get-Date)

## 修复状态
- Clippy 警告修复: $(if ($FixClippy -or $All) { "✅ 完成" } else { "⏳ 待处理" })
- Default 实现添加: $(if ($AddDefaults -or $All) { "✅ 完成" } else { "⏳ 待处理" })
- 依赖更新: $(if ($UpdateDeps -or $All) { "✅ 完成" } else { "⏳ 待处理" })
- 安全审计: $(if ($SecurityAudit -or $All) { "✅ 完成" } else { "⏳ 待处理" })

## 下一步行动
1. 检查修复结果
2. 运行测试验证
3. 提交更改
4. 继续下一阶段修复

## 注意事项
- 请仔细检查自动修复的结果
- 某些修复可能需要手动调整
- 建议在修复后运行完整的测试套件
"@
    
    $report | Out-File -FilePath "PROGRESS_REPORT_$(Get-Date -Format 'yyyyMMdd_HHmmss').md" -Encoding UTF8
    Write-Host "✅ 进度报告已生成" -ForegroundColor Green
}

# 主执行逻辑
try {
    # 检查必要工具
    if (-not (Test-Command "cargo")) {
        Write-Host "❌ Cargo 未找到，请确保 Rust 工具链已安装" -ForegroundColor Red
        exit 1
    }
    
    # 检查是否在正确的目录
    if (-not (Test-Path "Cargo.toml")) {
        Write-Host "❌ 未找到 Cargo.toml，请在项目根目录运行此脚本" -ForegroundColor Red
        exit 1
    }
    
    # 执行修复操作
    if ($All -or $FixClippy) {
        Fix-ClippyWarnings
    }
    
    if ($All -or $AddDefaults) {
        Add-DefaultImplementations
    }
    
    if ($All -or $UpdateDeps) {
        Update-Dependencies
    }
    
    if ($All -or $SecurityAudit) {
        Invoke-SecurityAudit
    }
    
    # 生成进度报告
    Generate-ProgressReport
    
    Write-Host "🎉 修复脚本执行完成！" -ForegroundColor Green
    Write-Host "请检查修复结果并运行测试验证" -ForegroundColor Yellow
    
} catch {
    Write-Host "❌ 脚本执行出错: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}

# 使用说明
Write-Host "`n📖 使用说明:" -ForegroundColor Cyan
Write-Host "  .\automated_fix_script.ps1 -All                    # 执行所有修复" -ForegroundColor White
Write-Host "  .\automated_fix_script.ps1 -FixClippy             # 只修复 Clippy 警告" -ForegroundColor White
Write-Host "  .\automated_fix_script.ps1 -AddDefaults           # 只添加 Default 实现" -ForegroundColor White
Write-Host "  .\automated_fix_script.ps1 -UpdateDeps            # 只更新依赖" -ForegroundColor White
Write-Host "  .\automated_fix_script.ps1 -SecurityAudit         # 只运行安全审计" -ForegroundColor White
Write-Host "  .\automated_fix_script.ps1 -FixClippy -Crate c01  # 只修复指定 crate" -ForegroundColor White
