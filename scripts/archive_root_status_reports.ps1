# 清理根目录：删除已归档到 docs/archive/root_completion_reports/ 的 .md 报告
# 仅删除「在归档目录中已存在同名文件」的根目录文件，保留 README、PROJECT_STRUCTURE、MIGRATION_GUIDE
# 用法：在仓库根目录执行 .\scripts\archive_root_status_reports.ps1

$ErrorActionPreference = "Stop"
# 脚本位于 scripts/，项目根目录为其父目录
$root = Split-Path $PSScriptRoot -Parent
$archiveDir = Join-Path $root "docs\archive\root_completion_reports"
$keep = @('README.md','README.en.md','PROJECT_STRUCTURE.md','MIGRATION_GUIDE_1.91.1_TO_1.92.0.md')

if (-not (Test-Path $archiveDir)) {
    Write-Host "归档目录不存在: $archiveDir"
    exit 0
}

$archived = Get-ChildItem $archiveDir -Filter "*.md" -File | Select-Object -ExpandProperty Name
$removed = 0
foreach ($name in $archived) {
    if ($name -in $keep) { continue }
    $path = Join-Path $root $name
    if (Test-Path $path) {
        Remove-Item $path -Force
        Write-Host "已删除(已归档): $name"
        $removed++
    }
}
Write-Host "共从根目录移除 $removed 个已归档文件。"
