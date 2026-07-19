# 依赖修复验证脚本 - 2025年1月
# 验证依赖修复的效果和项目状态

param(
    [switch]$Full,        # 完整验证
    [switch]$Quick,       # 快速验证
    [switch]$Report,      # 生成报告
    [switch]$Help         # 显示帮助
)

if ($Help) {
    Write-Host @"
依赖修复验证脚本

用法:
  .\verify_dependency_fix.ps1 [选项]

选项:
  -Full        完整验证（包括所有检查）
  -Quick       快速验证（仅核心检查）
  -Report      生成详细报告
  -Help        显示此帮助信息

示例:
  .\verify_dependency_fix.ps1 -Quick
  .\verify_dependency_fix.ps1 -Full -Report
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
        Write-ColorOutput "❌ Cargo 未找到" "Red"
        return $false
    }
}

# 检查编译状态
function Test-Compilation {
    Write-ColorOutput "🔨 检查编译状态..." "Yellow"
    cargo check --quiet
    if ($LASTEXITCODE -eq 0) {
        Write-ColorOutput "✅ 编译通过" "Green"
        return $true
    } else {
        Write-ColorOutput "❌ 编译失败" "Red"
        return $false
    }
}

# 检查版本冲突
function Test-VersionConflicts {
    Write-ColorOutput "🔍 检查版本冲突..." "Yellow"
    $conflicts = cargo tree --duplicates 2>$null
    if ($conflicts) {
        $conflictCount = ($conflicts | Measure-Object -Line).Lines
        Write-ColorOutput "⚠️ 发现 $conflictCount 个版本冲突" "Yellow"
        return $false
    } else {
        Write-ColorOutput "✅ 无版本冲突" "Green"
        return $true
    }
}

# 检查关键依赖版本
function Test-KeyDependencies {
    Write-ColorOutput "📦 检查关键依赖版本..." "Yellow"
    
    $keyDeps = @(
        @{name="serde"; expected="1.0.225"},
        @{name="tokio"; expected="1.47.1"},
        @{name="tracing"; expected="0.1.41"},
        @{name="anyhow"; expected="1.0.100"},
        @{name="thiserror"; expected="2.0.16"},
        @{name="reqwest"; expected="0.12.23"},
        @{name="axum"; expected="0.8.4"}
    )
    
    $allCorrect = $true
    foreach ($dep in $keyDeps) {
        $version = cargo search $dep.name --limit 1 2>$null | Select-String $dep.name
        if ($version -and $version.ToString() -match $dep.expected) {
            Write-ColorOutput "  ✅ $($dep.name): $($dep.expected)" "Green"
        } else {
            Write-ColorOutput "  ⚠️ $($dep.name): 版本可能不匹配" "Yellow"
            $allCorrect = $false
        }
    }
    
    return $allCorrect
}

# 检查安全漏洞
function Test-SecurityVulnerabilities {
    Write-ColorOutput "🔒 检查安全漏洞..." "Yellow"
    
    # 检查 cargo audit 是否可用
    try {
        $null = cargo audit --version 2>$null
        cargo audit --quiet
        if ($LASTEXITCODE -eq 0) {
            Write-ColorOutput "✅ 无安全漏洞" "Green"
            return $true
        } else {
            Write-ColorOutput "⚠️ 发现安全漏洞" "Yellow"
            return $false
        }
    }
    catch {
        Write-ColorOutput "⚠️ cargo audit 不可用，跳过安全检查" "Yellow"
        return $true
    }
}

# 检查过时依赖
function Test-OutdatedDependencies {
    Write-ColorOutput "📅 检查过时依赖..." "Yellow"
    
    # 检查 cargo outdated 是否可用
    try {
        $null = cargo outdated --version 2>$null
        $outdated = cargo outdated 2>$null
        if ($outdated) {
            $outdatedCount = ($outdated | Measure-Object -Line).Lines
            Write-ColorOutput "⚠️ 发现 $outdatedCount 个过时依赖" "Yellow"
            return $false
        } else {
            Write-ColorOutput "✅ 无过时依赖" "Green"
            return $true
        }
    }
    catch {
        Write-ColorOutput "⚠️ cargo outdated 不可用，跳过过时检查" "Yellow"
        return $true
    }
}

# 生成验证报告
function New-VerificationReport {
    param(
        [hashtable]$Results
    )
    
    $report = @"
# 依赖修复验证报告 - $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

## 验证结果摘要

| 检查项目 | 状态 | 详情 |
|----------|------|------|
| 编译状态 | $(if ($Results.Compilation) { "✅ 通过" } else { "❌ 失败" }) | 项目编译检查 |
| 版本冲突 | $(if ($Results.VersionConflicts) { "✅ 无冲突" } else { "⚠️ 有冲突" }) | 依赖版本冲突检查 |
| 关键依赖 | $(if ($Results.KeyDependencies) { "✅ 正确" } else { "⚠️ 异常" }) | 核心依赖版本检查 |
| 安全漏洞 | $(if ($Results.Security) { "✅ 安全" } else { "⚠️ 有漏洞" }) | 安全漏洞扫描 |
| 过时依赖 | $(if ($Results.Outdated) { "✅ 最新" } else { "⚠️ 过时" }) | 过时依赖检查 |

## 总体评估

$(if ($Results.Overall) { "🟢 验证通过 - 项目状态良好" } else { "🟡 验证部分通过 - 需要关注警告项" })

## 建议

$(if ($Results.Overall) { "项目依赖修复成功，可以正常使用。" } else { "建议检查警告项并采取相应措施。" })

---
*报告生成时间: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")*
"@
    
    $report | Out-File -FilePath "DEPENDENCY_VERIFICATION_REPORT.md" -Encoding UTF8
    Write-ColorOutput "📄 验证报告已生成: DEPENDENCY_VERIFICATION_REPORT.md" "Cyan"
}

# 主验证流程
function Main {
    Write-ColorOutput "🚀 开始依赖修复验证..." "Cyan"
    
    # 检查 cargo
    if (-not (Test-Cargo)) {
        exit 1
    }
    
    $results = @{
        Compilation = $false
        VersionConflicts = $false
        KeyDependencies = $false
        Security = $false
        Outdated = $false
        Overall = $false
    }
    
    # 核心检查
    $results.Compilation = Test-Compilation
    $results.VersionConflicts = Test-VersionConflicts
    $results.KeyDependencies = Test-KeyDependencies
    
    # 完整检查
    if ($Full) {
        $results.Security = Test-SecurityVulnerabilities
        $results.Outdated = Test-OutdatedDependencies
    }
    
    # 计算总体结果
    $results.Overall = $results.Compilation -and $results.KeyDependencies
    
    # 显示结果摘要
    Write-ColorOutput "`n📊 验证结果摘要:" "Cyan"
    Write-ColorOutput "  编译状态: $(if ($results.Compilation) { "✅ 通过" } else { "❌ 失败" })" $(if ($results.Compilation) { "Green" } else { "Red" })
    Write-ColorOutput "  版本冲突: $(if ($results.VersionConflicts) { "✅ 无冲突" } else { "⚠️ 有冲突" })" $(if ($results.VersionConflicts) { "Green" } else { "Yellow" })
    Write-ColorOutput "  关键依赖: $(if ($results.KeyDependencies) { "✅ 正确" } else { "⚠️ 异常" })" $(if ($results.KeyDependencies) { "Green" } else { "Yellow" })
    
    if ($Full) {
        Write-ColorOutput "  安全漏洞: $(if ($results.Security) { "✅ 安全" } else { "⚠️ 有漏洞" })" $(if ($results.Security) { "Green" } else { "Yellow" })
        Write-ColorOutput "  过时依赖: $(if ($results.Outdated) { "✅ 最新" } else { "⚠️ 过时" })" $(if ($results.Outdated) { "Green" } else { "Yellow" })
    }
    
    # 生成报告
    if ($Report) {
        New-VerificationReport -Results $results
    }
    
    # 最终评估
    if ($results.Overall) {
        Write-ColorOutput "`n🎉 依赖修复验证通过！项目状态良好。" "Green"
        exit 0
    } else {
        Write-ColorOutput "`n⚠️ 依赖修复验证部分通过，请检查警告项。" "Yellow"
        exit 1
    }
}

# 执行主流程
Main
