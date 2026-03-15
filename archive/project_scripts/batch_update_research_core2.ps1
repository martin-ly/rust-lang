# 第二批批量更新 docs/research_notes/

$files = @(
    "DOMAIN_ANALYSIS_FRAMEWORK.md",
    "ERROR_HANDLING_CHEATSHEET.md",
    "EXECUTABLE_SEMANTICS_ROADMAP.md",
    "FAQ.md",
    "FAQ_COMPREHENSIVE.md",
    "FEATURE_TEMPLATE.md",
    "FORMAL_ARGUMENTATION_COMPLETION_REPORT.md",
    "FORMAL_CONCEPTS_ENCYCLOPEDIA.md",
    "FORMAL_FULL_MODEL_EN_SUMMARY.md",
    "FORMAL_FULL_MODEL_OVERVIEW.md",
    "FORMAL_LANGUAGE_AND_PROOFS.md",
    "FORMAL_PROOF_SYSTEM_GUIDE.md",
    "FORMAL_VERIFICATION_GUIDE.md",
    "FORMAL_VERIFICATION_PRACTICAL_GUIDE.md",
    "GLOSSARY.md",
    "HIERARCHICAL_MAPPING_AND_SUMMARY.md",
    "INCREMENTAL_UPDATE_FLOW.md",
    "INDEX.md",
    "LEARNING_PATH_COMPREHENSIVE.md",
    "LIFETIME_CHEATSHEET.md"
)

$section = @"

---

## 🆕 Rust 1.94 更新

> **适用版本**: Rust 1.94.0+

详见 [RUST_194_RESEARCH_UPDATE](./RUST_194_RESEARCH_UPDATE.md)

**最后更新**: 2026-03-14
"@

$count = 0
foreach ($file in $files) {
    $path = "docs/research_notes/$file"
    if (Test-Path $path) {
        $content = Get-Content $path -Raw
        
        if (-not ($content -match "Rust 1\.94")) {
            $content = $content + $section
            Set-Content $path $content -NoNewline
            Write-Host "✅ 已更新: $file"
            $count++
        } else {
            Write-Host "⏭️  跳过: $file"
        }
    }
}

Write-Host "`n✅ 更新了 $count 个文件"
