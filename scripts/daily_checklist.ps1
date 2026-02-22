# 每日任务检查清单脚本 (PowerShell)
# 用法: .\scripts\daily_checklist.ps1

Write-Host "==================================" -ForegroundColor Cyan
Write-Host "每日任务检查清单 - $(Get-Date -Format 'yyyy-MM-dd')" -ForegroundColor Cyan
Write-Host "==================================" -ForegroundColor Cyan
Write-Host ""

# 检查Coq文件编译状态
Write-Host "📋 1. Coq文件编译检查" -ForegroundColor Yellow
Write-Host "----------------------"
$coqFound = Get-Command coqc -ErrorAction SilentlyContinue
if ($coqFound) {
    Push-Location docs/research_notes/coq_skeleton -ErrorAction SilentlyContinue
    if ($?) {
        Get-ChildItem -Filter "*.v" | ForEach-Object {
            Write-Host "  检查 $($_.Name): " -NoNewline
            $result = coqc -quiet $_.Name 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✅ 编译通过" -ForegroundColor Green
            } else {
                Write-Host "❌ 编译失败" -ForegroundColor Red
            }
        }
        Pop-Location
    }
} else {
    Write-Host "  ⚠️  Coq未安装，跳过编译检查" -ForegroundColor Yellow
}
Write-Host ""

# 统计Admitted数量
Write-Host "📋 2. Coq证明完成度统计" -ForegroundColor Yellow
Write-Host "----------------------"
Push-Location docs/research_notes/coq_skeleton -ErrorAction SilentlyContinue
if ($?) {
    Get-ChildItem -Filter "*.v" | ForEach-Object {
        $content = Get-Content $_.Name -Raw
        $admittedCount = ([regex]::Matches($content, "Admitted")).Count
        $qedCount = ([regex]::Matches($content, "Qed")).Count
        Write-Host "  $($_.Name): Admitted=$admittedCount, Qed=$qedCount"
    }
    Pop-Location
} else {
    Write-Host "  ⚠️  未找到Coq文件" -ForegroundColor Yellow
}
Write-Host ""

# 检查Markdown文件格式
Write-Host "📋 3. Markdown文件格式检查" -ForegroundColor Yellow
Write-Host "----------------------"
$invalidTables = 0
Get-ChildItem -Path docs/research_notes -Recurse -Filter "*.md" | ForEach-Object {
    $content = Get-Content $_.FullName -Raw
    if ($content -match "\|:\-+[^\s]" -or $content -match "\|:\-[^:]\|") {
        $invalidTables++
    }
}
if ($invalidTables -eq 0) {
    Write-Host "  ✅ 表格格式正确" -ForegroundColor Green
} else {
    Write-Host "  ⚠️  发现 $invalidTables 处表格格式问题" -ForegroundColor Yellow
}
Write-Host ""

# 统计文档数量
Write-Host "📋 4. 文档资产统计" -ForegroundColor Yellow
Write-Host "----------------------"
$formalMethodsCount = (Get-ChildItem -Path docs/research_notes/formal_methods -Filter "*.md" -Recurse -ErrorAction SilentlyContinue).Count
$softwareDesignCount = (Get-ChildItem -Path docs/research_notes/software_design_theory -Filter "*.md" -Recurse -ErrorAction SilentlyContinue).Count
$typeTheoryCount = (Get-ChildItem -Path docs/research_notes/type_theory -Filter "*.md" -Recurse -ErrorAction SilentlyContinue).Count
$coqFilesCount = (Get-ChildItem -Path docs/research_notes/coq_skeleton -Filter "*.v" -ErrorAction SilentlyContinue).Count

Write-Host "  formal_methods文档: $formalMethodsCount"
Write-Host "  software_design_theory文档: $softwareDesignCount"
Write-Host "  type_theory文档: $typeTheoryCount"
Write-Host "  Coq文件: $coqFilesCount"
Write-Host ""

# 检查本周任务进度
Write-Host "📋 5. 本周任务检查" -ForegroundColor Yellow
Write-Host "----------------------"
Write-Host "  Week 1目标: OWNERSHIP_UNIQUENESS.v 编译通过，Admitted ≤ 5"
$owFile = "docs/research_notes/coq_skeleton/OWNERSHIP_UNIQUENESS.v"
if (Test-Path $owFile) {
    $content = Get-Content $owFile -Raw
    $owAdmitted = ([regex]::Matches($content, "Admitted")).Count
    Write-Host "  当前Admitted数量: $owAdmitted"
    if ($owAdmitted -le 5) {
        Write-Host "  ✅ Week 1目标达成" -ForegroundColor Green
    } else {
        $remaining = $owAdmitted - 5
        Write-Host "  🔄 还需完成 $remaining 个证明" -ForegroundColor Yellow
    }
}
Write-Host ""

# Git状态检查
Write-Host "📋 6. Git提交检查" -ForegroundColor Yellow
Write-Host "----------------------"
if (Test-Path .git) {
    $status = git status --porcelain
    $uncommitted = ($status | Measure-Object).Count
    if ($uncommitted -eq 0) {
        Write-Host "  ✅ 所有更改已提交" -ForegroundColor Green
    } else {
        Write-Host "  📝 有 $uncommitted 个未提交更改" -ForegroundColor Yellow
        git status --short
    }
} else {
    Write-Host "  ⚠️  非Git仓库" -ForegroundColor Yellow
}
Write-Host ""

Write-Host "==================================" -ForegroundColor Cyan
Write-Host "检查完成 - 继续推进100%完成!" -ForegroundColor Cyan
Write-Host "==================================" -ForegroundColor Cyan
