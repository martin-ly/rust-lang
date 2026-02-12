# 文档链接检查脚本 / Document Link Check Script
# 用途：检查 Markdown 文档中的断链
# 使用：.\scripts\check_links.ps1
# 依赖：若已安装 cargo-deadlinks，可执行 cargo deadlinks; 本脚本提供基础检查

param(
    [switch]$UseDeadlinks
)

$ErrorActionPreference = "Continue"
$root = $PSScriptRoot

if ($UseDeadlinks) {
    Write-Host "检查: cargo deadlinks..." -ForegroundColor Cyan
    cargo deadlinks 2>&1
    exit $LASTEXITCODE
}

# 简单检查：查找可能断链的路径模式
Write-Host "基础链接检查: 查找 tier3_advanced、tier1_foundation 等旧路径..." -ForegroundColor Cyan
$oldPatterns = @(
    "tier3_advanced",
    "tier1_foundation",
    "tier2_core_concepts",
    "tier4_theoretical"
)
$found = $false
foreach ($pattern in $oldPatterns) {
    $matches = Get-ChildItem -Path $root -Recurse -Include "*.md" -ErrorAction SilentlyContinue | 
        Select-String -Pattern $pattern -ErrorAction SilentlyContinue
    if ($matches) {
        $found = $true
        Write-Host "  [警告] 发现旧路径 '$pattern':" -ForegroundColor Yellow
        $matches | ForEach-Object { Write-Host "    $($_.Path):$($_.LineNumber)" }
    }
}
if (-not $found) {
    Write-Host "  未发现旧路径引用" -ForegroundColor Green
}

Write-Host "`n提示: 安装 cargo-deadlinks 后可使用 -UseDeadlinks 进行完整检查" -ForegroundColor Gray
Write-Host "  cargo install cargo-deadlinks" -ForegroundColor Gray
Write-Host "  .\scripts\check_links.ps1 -UseDeadlinks" -ForegroundColor Gray
