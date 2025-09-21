# Rust 依赖版本更新脚本 - 2025年1月
# 用于检查和更新项目依赖版本

param(
    [switch]$CheckOnly,      # 仅检查，不更新
    [switch]$FixConflicts,   # 修复版本冲突
    [switch]$UpdateAll,      # 更新所有依赖
    [switch]$Audit,          # 安全审计
    [switch]$Clean,          # 清理未使用依赖
    [switch]$Help            # 显示帮助
)

if ($Help) {
    Write-Host @"
Rust 依赖版本更新脚本

用法:
  .\dependency_version_update.ps1 [选项]

选项:
  -CheckOnly      仅检查依赖状态，不进行更新
  -FixConflicts   修复版本冲突
  -UpdateAll      更新所有依赖到最新版本
  -Audit          执行安全审计
  -Clean          清理未使用的依赖
  -Help           显示此帮助信息

示例:
  .\dependency_version_update.ps1 -CheckOnly
  .\dependency_version_update.ps1 -FixConflicts -Audit
  .\dependency_version_update.ps1 -UpdateAll -Clean
"@
    exit 0
}

# 颜色输出函数
function Write-ColorOutput {
    param(
        [string]$Message,
        [string]$Color = "White"
    )
    Write-Host $Message -ForegroundColor $Color
}

# 检查 cargo 是否可用
function Test-Cargo {
    try {
        $null = cargo --version
        return $true
    }
    catch {
        Write-ColorOutput "错误: 未找到 cargo 命令" "Red"
        return $false
    }
}

# 检查依赖版本冲突
function Test-DependencyConflicts {
    Write-ColorOutput "`n🔍 检查依赖版本冲突..." "Cyan"
    
    $duplicates = cargo tree --duplicates 2>$null
    if ($LASTEXITCODE -eq 0 -and $duplicates) {
        Write-ColorOutput "发现以下版本冲突:" "Yellow"
        Write-Host $duplicates
        return $true
    } else {
        Write-ColorOutput "✅ 未发现版本冲突" "Green"
        return $false
    }
}

# 检查过时依赖
function Test-OutdatedDependencies {
    Write-ColorOutput "`n🔍 检查过时依赖..." "Cyan"
    
    # 检查是否安装了 cargo-outdated
    $outdatedInstalled = cargo install --list | Select-String "cargo-outdated"
    if (-not $outdatedInstalled) {
        Write-ColorOutput "安装 cargo-outdated..." "Yellow"
        cargo install cargo-outdated
    }
    
    if ($LASTEXITCODE -eq 0) {
        cargo outdated
    } else {
        Write-ColorOutput "⚠️  无法检查过时依赖，请手动安装 cargo-outdated" "Yellow"
    }
}

# 执行安全审计
function Invoke-SecurityAudit {
    Write-ColorOutput "`n🔒 执行安全审计..." "Cyan"
    
    # 检查是否安装了 cargo-audit
    $auditInstalled = cargo install --list | Select-String "cargo-audit"
    if (-not $auditInstalled) {
        Write-ColorOutput "安装 cargo-audit..." "Yellow"
        cargo install cargo-audit
    }
    
    if ($LASTEXITCODE -eq 0) {
        cargo audit
        if ($LASTEXITCODE -eq 0) {
            Write-ColorOutput "✅ 安全审计通过" "Green"
        } else {
            Write-ColorOutput "⚠️  发现安全漏洞，请查看上述报告" "Yellow"
        }
    } else {
        Write-ColorOutput "⚠️  无法执行安全审计，请手动安装 cargo-audit" "Yellow"
    }
}

# 清理未使用依赖
function Remove-UnusedDependencies {
    Write-ColorOutput "`n🧹 清理未使用依赖..." "Cyan"
    
    # 检查是否安装了 cargo-machete
    $macheteInstalled = cargo install --list | Select-String "cargo-machete"
    if (-not $macheteInstalled) {
        Write-ColorOutput "安装 cargo-machete..." "Yellow"
        cargo install cargo-machete
    }
    
    if ($LASTEXITCODE -eq 0) {
        Write-ColorOutput "扫描未使用的依赖..." "Yellow"
        cargo machete
    } else {
        Write-ColorOutput "⚠️  无法清理未使用依赖，请手动安装 cargo-machete" "Yellow"
    }
}

# 修复版本冲突
function Repair-VersionConflicts {
    Write-ColorOutput "`n🔧 修复版本冲突..." "Cyan"
    
    # 创建版本覆盖配置
    $patchConfig = @"
# 版本冲突修复配置
[patch.crates-io]
# 强制使用最新版本
serde = "1.0.225"
thiserror = "2.0.16"
tokio-rustls = "0.26.3"
prost = "0.14.1"
rand = "0.9.2"
toml = "0.9.7"
rustls = "0.23.32"
rustls-webpki = "0.104.1"
"@
    
    # 检查根 Cargo.toml 是否已有 patch 配置
    $cargoToml = Get-Content "Cargo.toml" -Raw
    if ($cargoToml -notmatch "\[patch\.crates-io\]") {
        Write-ColorOutput "添加版本覆盖配置到 Cargo.toml..." "Yellow"
        Add-Content "Cargo.toml" "`n$patchConfig"
    } else {
        Write-ColorOutput "⚠️  Cargo.toml 中已存在 patch 配置，请手动检查" "Yellow"
    }
    
    # 更新 Cargo.lock
    Write-ColorOutput "更新 Cargo.lock..." "Yellow"
    cargo update
}

# 更新所有依赖
function Update-AllDependencies {
    Write-ColorOutput "`n📦 更新所有依赖..." "Cyan"
    
    Write-ColorOutput "更新 Cargo.lock..." "Yellow"
    cargo update
    
    if ($LASTEXITCODE -eq 0) {
        Write-ColorOutput "✅ 依赖更新完成" "Green"
    } else {
        Write-ColorOutput "❌ 依赖更新失败" "Red"
    }
}

# 生成依赖报告
function New-DependencyReport {
    Write-ColorOutput "`n📊 生成依赖报告..." "Cyan"
    
    $reportFile = "DEPENDENCY_REPORT_$(Get-Date -Format 'yyyy-MM-dd_HH-mm-ss').md"
    
    $report = @"
# 依赖分析报告 - $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')

## 依赖树
``````
$(cargo tree)
``````

## 版本冲突
``````
$(cargo tree --duplicates)
``````

## 过时依赖
``````
$(cargo outdated 2>$null)
``````

## 安全审计结果
``````
$(cargo audit 2>$null)
``````
"@
    
    $report | Out-File -FilePath $reportFile -Encoding UTF8
    Write-ColorOutput "报告已保存到: $reportFile" "Green"
}

# 主执行逻辑
function Main {
    Write-ColorOutput "🚀 Rust 依赖版本管理工具" "Magenta"
    Write-ColorOutput "================================" "Magenta"
    
    if (-not (Test-Cargo)) {
        exit 1
    }
    
    # 检查当前目录是否为 Rust 项目
    if (-not (Test-Path "Cargo.toml")) {
        Write-ColorOutput "错误: 当前目录不是 Rust 项目根目录" "Red"
        exit 1
    }
    
    $hasConflicts = Test-DependencyConflicts
    
    if ($CheckOnly) {
        Test-OutdatedDependencies
        New-DependencyReport
        return
    }
    
    if ($Audit) {
        Invoke-SecurityAudit
    }
    
    if ($Clean) {
        Remove-UnusedDependencies
    }
    
    if ($FixConflicts -and $hasConflicts) {
        Repair-VersionConflicts
    }
    
    if ($UpdateAll) {
        Update-AllDependencies
    }
    
    # 如果没有指定任何操作，执行完整检查
    if (-not ($CheckOnly -or $FixConflicts -or $UpdateAll -or $Audit -or $Clean)) {
        Write-ColorOutput "`n执行完整依赖检查..." "Cyan"
        Test-DependencyConflicts
        Test-OutdatedDependencies
        Invoke-SecurityAudit
        New-DependencyReport
    }
    
    Write-ColorOutput "`n✅ 依赖管理完成" "Green"
}

# 执行主函数
Main
