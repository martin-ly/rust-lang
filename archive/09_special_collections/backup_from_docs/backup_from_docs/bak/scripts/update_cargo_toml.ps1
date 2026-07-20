# Cargo.toml 依赖更新脚本
# 用于将 cargo update 的更新同步到 Cargo.toml 文件

param(
    [switch]$DryRun = $false,
    [switch]$Backup = $true,
    [string]$WorkspacePath = "."
)

Write-Host "🚀 开始 Cargo.toml 依赖更新流程..." -ForegroundColor Green

# 函数：备份文件
function Backup-File {
    param([string]$FilePath)
    
    if (Test-Path $FilePath) {
        $backupPath = "$FilePath.backup.$(Get-Date -Format 'yyyyMMdd_HHmmss')"
        Copy-Item $FilePath $backupPath -Force
        Write-Host "✅ 已备份: $FilePath -> $backupPath" -ForegroundColor Yellow
        return $backupPath
    }
    return $null
}

# 函数：获取 Cargo.lock 中的版本信息
function Get-LockVersions {
    param([string]$LockFile)
    
    if (-not (Test-Path $LockFile)) {
        Write-Host "❌ Cargo.lock 文件不存在: $LockFile" -ForegroundColor Red
        return @{}
    }
    
    $versions = @{}
    $content = Get-Content $LockFile -Raw
    
    # 解析 Cargo.lock 中的版本信息
    $pattern = 'name = "([^"]+)"\s+version = "([^"]+)"'
    $matches = [regex]::Matches($content, $pattern)
    
    foreach ($match in $matches) {
        $name = $match.Groups[1].Value
        $version = $match.Groups[2].Value
        $versions[$name] = $version
    }
    
    Write-Host "📦 从 Cargo.lock 中提取了 $($versions.Count) 个依赖版本" -ForegroundColor Cyan
    return $versions
}

# 函数：更新 Cargo.toml 文件
function Update-CargoToml {
    param(
        [string]$TomlFile,
        [hashtable]$Versions,
        [bool]$DryRun
    )
    
    if (-not (Test-Path $TomlFile)) {
        Write-Host "⚠️  Cargo.toml 文件不存在: $TomlFile" -ForegroundColor Yellow
        return
    }
    
    Write-Host "🔍 处理文件: $TomlFile" -ForegroundColor Cyan
    
    $content = Get-Content $TomlFile -Raw
    $originalContent = $content
    $updatedCount = 0
    
    # 更新 [dependencies] 部分
    $depsPattern = '(\[dependencies\]\s*)(.*?)(?=\[|\Z)'
    $depsMatch = [regex]::Match($content, $depsPattern, [System.Text.RegularExpressions.RegexOptions]::Singleline)
    
    if ($depsMatch.Success) {
        $depsSection = $depsMatch.Groups[2].Value
        $newDepsSection = $depsSection
        
        # 更新每个依赖的版本
        foreach ($depName in $Versions.Keys) {
            $newVersion = $Versions[$depName]
            
            # 匹配依赖行
            $depPattern = "($depName\s*=\s*`"[^`"]*`")"
            $depMatch = [regex]::Match($newDepsSection, $depPattern)
            
            if ($depMatch.Success) {
                $oldDep = $depMatch.Groups[1].Value
                $newDep = "$depName = `"$newVersion`""
                
                if ($oldDep -ne $newDep) {
                    $newDepsSection = $newDepsSection -replace [regex]::Escape($oldDep), $newDep
                    $updatedCount++
                    Write-Host "  📝 更新依赖: $depName -> $newVersion" -ForegroundColor Green
                }
            }
        }
        
        # 替换整个 dependencies 部分
        $newContent = $content -replace [regex]::Escape($depsMatch.Groups[0].Value), "$($depsMatch.Groups[1].Value)$newDepsSection"
        $content = $newContent
    }
    
    # 更新 [dev-dependencies] 部分
    $devDepsPattern = '(\[dev-dependencies\]\s*)(.*?)(?=\[|\Z)'
    $devDepsMatch = [regex]::Match($content, $devDepsPattern, [System.Text.RegularExpressions.RegexOptions]::Singleline)
    
    if ($devDepsMatch.Success) {
        $devDepsSection = $devDepsMatch.Groups[2].Value
        $newDevDepsSection = $devDepsSection
        
        # 更新每个开发依赖的版本
        foreach ($depName in $Versions.Keys) {
            $newVersion = $Versions[$depName]
            
            # 匹配开发依赖行
            $depPattern = "($depName\s*=\s*`"[^`"]*`")"
            $depMatch = [regex]::Match($newDevDepsSection, $depPattern)
            
            if ($depMatch.Success) {
                $oldDep = $depMatch.Groups[1].Value
                $newDep = "$depName = `"$newVersion`""
                
                if ($oldDep -ne $newDep) {
                    $newDevDepsSection = $newDevDepsSection -replace [regex]::Escape($oldDep), $newDep
                    $updatedCount++
                    Write-Host "  📝 更新开发依赖: $depName -> $newVersion" -ForegroundColor Green
                }
            }
        }
        
        # 替换整个 dev-dependencies 部分
        $newContent = $content -replace [regex]::Escape($devDepsMatch.Groups[0].Value), "$($devDepsMatch.Groups[1].Value)$newDevDepsSection"
        $content = $newContent
    }
    
    if ($updatedCount -gt 0) {
        if ($DryRun) {
            Write-Host "  🔍 预览模式: 将更新 $updatedCount 个依赖" -ForegroundColor Yellow
        } else {
            # 备份原文件
            if ($Backup) {
                Backup-File $TomlFile
            }
            
            # 写入更新后的内容
            Set-Content $TomlFile $content -Encoding UTF8
            Write-Host "  ✅ 已更新 $updatedCount 个依赖" -ForegroundColor Green
        }
    } else {
        Write-Host "  ℹ️  无需更新依赖" -ForegroundColor Blue
    }
}

# 主执行流程
try {
    # 1. 检查 Cargo.lock 文件
    $lockFile = Join-Path $WorkspacePath "Cargo.lock"
    if (-not (Test-Path $lockFile)) {
        Write-Host "❌ 未找到 Cargo.lock 文件，请先运行 'cargo update'" -ForegroundColor Red
        exit 1
    }
    
    # 2. 获取版本信息
    Write-Host "📦 从 Cargo.lock 提取版本信息..." -ForegroundColor Cyan
    $versions = Get-LockVersions $lockFile
    
    if ($versions.Count -eq 0) {
        Write-Host "⚠️  未找到版本信息" -ForegroundColor Yellow
        exit 0
    }
    
    # 3. 查找所有 Cargo.toml 文件
    $tomlFiles = Get-ChildItem -Path $WorkspacePath -Name "Cargo.toml" -Recurse
    
    if ($tomlFiles.Count -eq 0) {
        Write-Host "❌ 未找到 Cargo.toml 文件" -ForegroundColor Red
        exit 1
    }
    
    Write-Host "📁 找到 $($tomlFiles.Count) 个 Cargo.toml 文件" -ForegroundColor Cyan
    
    # 4. 更新每个 Cargo.toml 文件
    $totalUpdated = 0
    foreach ($tomlFile in $tomlFiles) {
        $fullPath = Join-Path $WorkspacePath $tomlFile
        Update-CargoToml $fullPath $versions $DryRun
    }
    
    # 5. 验证更新结果
    if (-not $DryRun) {
        Write-Host "🔍 验证更新结果..." -ForegroundColor Cyan
        
        # 检查编译
        $checkResult = & cargo check --workspace 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✅ 编译检查通过" -ForegroundColor Green
        } else {
            Write-Host "❌ 编译检查失败" -ForegroundColor Red
            Write-Host $checkResult -ForegroundColor Red
        }
        
        # 检查过时依赖
        Write-Host "📊 检查过时依赖..." -ForegroundColor Cyan
        $outdatedResult = & cargo outdated --workspace 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✅ 依赖检查完成" -ForegroundColor Green
        } else {
            Write-Host "⚠️  依赖检查警告" -ForegroundColor Yellow
        }
    }
    
    Write-Host "🎉 Cargo.toml 依赖更新完成！" -ForegroundColor Green
    
    if ($DryRun) {
        Write-Host "💡 使用 -DryRun:$false 参数执行实际更新" -ForegroundColor Yellow
    }
    
} catch {
    Write-Host "❌ 更新过程中发生错误: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}

# 使用说明
Write-Host "`n📖 使用说明:" -ForegroundColor Cyan
Write-Host "  .\scripts\update_cargo_toml.ps1                    # 预览模式" -ForegroundColor White
Write-Host "  .\scripts\update_cargo_toml.ps1 -DryRun:`$false     # 执行更新" -ForegroundColor White
Write-Host "  .\scripts\update_cargo_toml.ps1 -Backup:`$false     # 不备份原文件" -ForegroundColor White
Write-Host "  .\scripts\update_cargo_toml.ps1 -WorkspacePath .    # 指定工作空间路径" -ForegroundColor White
