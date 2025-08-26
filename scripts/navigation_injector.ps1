Param(
    [Parameter(Mandatory=$false)] [string]$Root = (Get-Location).Path,
    [Parameter(Mandatory=$false)] [string[]]$IncludeExtensions = @('.md', '.rs'),
    [Parameter(Mandatory=$false)] [string[]]$ExcludeDirs = @('target', '.git', 'node_modules', '.cursor', '.vscode'),
    [switch]$CheckOnly
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

function Get-RelativePath([string]$from, [string]$to) {
    $fromUri = New-Object System.Uri((Resolve-Path -LiteralPath $from).Path)
    $toUri = New-Object System.Uri((Resolve-Path -LiteralPath $to).Path)
    $relUri = $fromUri.MakeRelativeUri($toUri)
    [System.Uri]::UnescapeDataString($relUri.ToString()).Replace('/', [System.IO.Path]::DirectorySeparatorChar)
}

$refactorRoot = Join-Path $Root 'formal_rust\refactor'
if (-not (Test-Path $refactorRoot)) {
    Write-Error "refactor 根目录不存在: $refactorRoot"
}

function Build-NavBlock([string]$fileDir) {
    $rel = Get-RelativePath $fileDir $refactorRoot
    if ([string]::IsNullOrWhiteSpace($rel)) { $rel = '.' }
    $global = Join-Path $rel '01_knowledge_graph/01_global_graph.md'
    $layered = Join-Path $rel '01_knowledge_graph/02_layered_graph.md'
    $index = Join-Path $rel '01_knowledge_graph/00_index.md'
    $map = Join-Path $rel '01_knowledge_graph/node_link_map.md'
@"
> 返回知识图谱：
>
> - 全局图谱: $global
> - 分层图谱: $layered
> - 索引与映射: $index, $map

---
"@
}

function Build-Footer([string]$fileDir) {
    $rel = Get-RelativePath $fileDir $refactorRoot
    if ([string]::IsNullOrWhiteSpace($rel)) { $rel = '.' }
    $map = Join-Path $rel '01_knowledge_graph/node_link_map.md'
    $snapshot = Join-Path $rel 'COMPREHENSIVE_KNOWLEDGE_GRAPH.md'
    "参考指引：节点映射见 $map；综合快照与导出见 $snapshot。"
}

function Build-CodeCommentHeader([string]$fileDir) {
    $rel = Get-RelativePath $fileDir $refactorRoot
    if ([string]::IsNullOrWhiteSpace($rel)) { $rel = '.' }
    $global = Join-Path $rel '01_knowledge_graph/01_global_graph.md'
    $layered = Join-Path $rel '01_knowledge_graph/02_layered_graph.md'
    $index = Join-Path $rel '01_knowledge_graph/00_index.md'
    $map = Join-Path $rel '01_knowledge_graph/node_link_map.md'
    $snapshot = Join-Path $rel 'COMPREHENSIVE_KNOWLEDGE_GRAPH.md'
@"
// 返回知识图谱：
// - 全局图谱: $global
// - 分层图谱: $layered
// - 索引与映射: $index, $map
// 参考指引：节点映射见 $map；综合快照与导出见 $snapshot。
"@
}

function Should-Exclude([string]$path) {
    foreach ($d in $ExcludeDirs) { if ($path -like "*\$d\*") { return $true } }
    return $false
}

$files = Get-ChildItem -LiteralPath $Root -Recurse -File | Where-Object {
    $ext = [System.IO.Path]::GetExtension($_.Name).ToLowerInvariant()
    ($IncludeExtensions -contains $ext) -and -not (Should-Exclude $_.FullName)
}

$updated = @()
$skipped = @()
$checked = 0

foreach ($f in $files) {
    $checked++
    $dir = Split-Path -Parent $f.FullName
    $ext = [System.IO.Path]::GetExtension($f.Name).ToLowerInvariant()
    $content = Get-Content -LiteralPath $f.FullName -Raw

    if ($content -match '返回知识图谱') {
        $skipped += $f.FullName
        continue
    }

    if ($CheckOnly) { continue }

    if ($ext -eq '.md') {
        $nav = Build-NavBlock $dir
        $footer = Build-Footer $dir
        $lines = $content -split "`n"
        $insertIdx = ($lines | Select-String -Pattern '^(#)+' | Select-Object -First 1).LineNumber
        if (-not $insertIdx) { $insertIdx = 1 }
        $before = $lines[0..($insertIdx-1)] -join "`n"
        $after = $lines[$insertIdx..($lines.Length-1)] -join "`n"
        $newContent = @($before.TrimEnd(), '---', $nav.TrimEnd(), '', $after.TrimEnd(), '', '---', $footer, '') -join "`n"
        Set-Content -LiteralPath $f.FullName -Value $newContent -NoNewline:$false -Encoding UTF8
        $updated += $f.FullName
    }
    elseif ($ext -eq '.rs') {
        $header = Build-CodeCommentHeader $dir
        $newContent = @($header.TrimEnd(), $content) -join "`n"
        Set-Content -LiteralPath $f.FullName -Value $newContent -NoNewline:$false -Encoding UTF8
        $updated += $f.FullName
    }
}

Write-Output ("检查文件数: {0}" -f $checked)
Write-Output ("已更新: {0}" -f $updated.Count)
Write-Output ("已存在导航(跳过): {0}" -f $skipped.Count)
if ($updated.Count -gt 0) { Write-Output '示例更新文件:'; $updated | Select-Object -First 10 }
