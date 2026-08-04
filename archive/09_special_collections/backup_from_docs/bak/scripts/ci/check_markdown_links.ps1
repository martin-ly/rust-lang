param(
    [string]$Root = (Resolve-Path "$PSScriptRoot\..\.."),
    [string]$Glob = "**/*.md"
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

Write-Host "Scanning markdown links under: $Root"

$mdFiles = Get-ChildItem -Path $Root -Recurse -Filter *.md -ErrorAction SilentlyContinue |
    Where-Object { $_.FullName -notmatch "language_backup|migration-backup|\\target\\" }

$total = 0
$broken = 0
$brokenList = New-Object System.Collections.Generic.List[object]
$byFile = @{}

function Remove-MarkdownCode {
    param([string]$Text)
    if ([string]::IsNullOrEmpty($Text)) { return $Text }
    # 移除围栏代码块 ```...```
    $noBlocks = [regex]::Replace($Text, '```[\s\S]*?```', '', [System.Text.RegularExpressions.RegexOptions]::Singleline)
    # 移除行内代码 `...`
    $noInline = [regex]::Replace($noBlocks, '`[^`]*`', '')
    return $noInline
}

function Test-MarkdownTargetExists {
    param(
        [string]$BaseDir,
        [string]$RefPath
    )
    if ([string]::IsNullOrWhiteSpace($RefPath)) { return $false }

    # 去掉锚点与查询参数
    $purePath = $RefPath.Split('#')[0].Split('?')[0]
    if ([string]::IsNullOrWhiteSpace($purePath)) { return $true } # 仅锚点，视为存在

    # 快速过滤：包含非法路径字符的引用直接视为不存在，避免 Test-Path 抛异常
    $invalidCharsPattern = '[\x00-\x1F"<>\|]'
    if ($purePath -match $invalidCharsPattern) { return $false }

    # 裸文本（无路径分隔符、无扩展名）通常表示同页锚点或概念引用，视为存在
    $hasSeparator = ($purePath -like '*/*' -or $purePath -like '*\\*')
    $hasExt = $false
    try { $hasExt = [System.IO.Path]::HasExtension($purePath) } catch { $hasExt = $false }
    if (-not $hasSeparator -and -not $hasExt) { return $true }

    # 规范化相对路径
    $candidate = Join-Path $BaseDir $purePath

    function SafeTestPathLeaf([string]$p) {
        try { return (Test-Path -LiteralPath $p -PathType Leaf) } catch { return $false }
    }
    function SafeTestPathContainer([string]$p) {
        try { return (Test-Path -LiteralPath $p -PathType Container) } catch { return $false }
    }

    function Resolve-ByBasename([string]$path) {
        try {
            $name = [System.IO.Path]::GetFileName($path)
            if ([string]::IsNullOrWhiteSpace($name)) { return $null }
            $candidates = Get-ChildItem -Path $Root -Recurse -Filter $name -ErrorAction SilentlyContinue | Select-Object -First 1
            if ($candidates) { return $candidates.FullName }
        } catch { }
        return $null
    }

    # 1) 直接命中文件
    if (SafeTestPathLeaf $candidate) { return $true }
    
    # 2) 无扩展时补全 .md
    if (-not [System.IO.Path]::HasExtension($candidate)) {
        $withMd = "$candidate.md"
        if (SafeTestPathLeaf $withMd) { return $true }
    }

    # 3) 目录链接命中 index 系列
    if (SafeTestPathContainer $candidate) {
        $indexFiles = @("index.md", "00_index.md", "_index.md", "README.md")
        foreach ($idx in $indexFiles) {
            $idxPath = Join-Path $candidate $idx
            if (SafeTestPathLeaf $idxPath) { return $true }
        }
    }

    # 4) 链接末尾有斜杠但目录未显式创建时，尝试去掉斜杠再补全 .md
    if ($candidate.EndsWith([System.IO.Path]::DirectorySeparatorChar) -or $candidate.EndsWith('/')) {
        $trimmed = $candidate.TrimEnd('\','/')
        if (SafeTestPathContainer $trimmed) {
            $indexFiles = @("index.md", "00_index.md", "_index.md", "README.md")
            foreach ($idx in $indexFiles) {
                $idxPath = Join-Path $trimmed $idx
                if (SafeTestPathLeaf $idxPath) { return $true }
            }
        }
        if (SafeTestPathLeaf ($trimmed + ".md")) { return $true }
    }

    # 5) 基于文件名的全局回退匹配（降低误报；可能产生少量假阳）
    $fallback = Resolve-ByBasename -path $purePath
    if ($fallback) { return $true }

    return $false
}

foreach ($file in $mdFiles) {
    $relDir = Split-Path -Parent $file.FullName
    try {
        $content = Get-Content -LiteralPath $file.FullName -Raw -ErrorAction Stop
    } catch {
        Write-Host "SKIP (read error): $($file.FullName)" -ForegroundColor Yellow
        continue
    }
    if ([string]::IsNullOrEmpty($content)) { continue }
    $content = Remove-MarkdownCode -Text $content

    # 匹配形如 [text](path) 的相对链接（排除 http/https/mailto）
    $linkMatches = [regex]::Matches($content, '\[[^\]]+\]\((?!https?://|mailto:)([^)\s>]+)\)')
    foreach ($m in $linkMatches) {
        $path = $m.Groups[1].Value
        $total++
        if (-not (Test-MarkdownTargetExists -BaseDir $relDir -RefPath $path)) {
            $broken++
            $entry = @{ source = $file.FullName; target = $path }
            [void]$brokenList.Add([pscustomobject]$entry)
            if (-not $byFile.ContainsKey($file.FullName)) { $byFile[$file.FullName] = 0 }
            $byFile[$file.FullName]++
        }
    }
}

try {
    $outDir = Join-Path $Root "target/tmp"
    New-Item -ItemType Directory -Force -Path $outDir | Out-Null
    $outFile = Join-Path $outDir "broken_links.txt"
    $brokenList | ForEach-Object { "BROKEN: $($_.source) -> $($_.target)" } | Set-Content -Encoding UTF8 -LiteralPath $outFile
    # Top 20 文件统计
    $top = $byFile.GetEnumerator() | Sort-Object -Property Value -Descending | Select-Object -First 20
    Write-Host "Top files with broken links:" -ForegroundColor Yellow
    foreach ($t in $top) {
        Write-Host ("{0} -> {1}" -f $t.Key, $t.Value) -ForegroundColor Yellow
    }
    Write-Host ("Report saved to: {0}" -f $outFile)
} catch {
    Write-Host "WARN: failed to write report: $($_.Exception.Message)" -ForegroundColor Yellow
}

Write-Host "Checked links: $total; Broken: $broken"
if ($broken -gt 0) { exit 1 } else { exit 0 }


