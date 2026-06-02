# PowerShell 脚本：批量更新历史版本文件标记
# 创建日期: 2025-12-11
# 用途: 批量更新所有 rust_189_*, rust_190_*, rust_191_* 文件的历史版本标记

$ErrorActionPreference = "Continue"

Write-Host "开始批量更新历史版本文件..." -ForegroundColor Green

# 定义需要替换的旧文本模式
$oldPattern189 = @"
//! # Rust 1.89 特性示例 (历史版本)
//!
//! ⚠️ **注意**: 本示例针对 Rust 1.89 版本编写，部分特性在 Rust 1.90 中已有更新。
//!
//! ## Rust 1.90 主要更新
//!
//! ### 编译器改进
//! - **LLD 链接器**: Linux x86_64 默认启用，链接速度提升约 2x
//! - **编译性能**: 增量编译优化，构建速度提升
//!
//! ### 标准库更新
//! - `u{n}::checked_sub_signed()` - 新增带符号减法检查方法
//! - `<[T]>::reverse()` - 现在可在 const 上下文中使用
//! - `f32/f64` 数学函数 - floor/ceil/trunc 等在 const 中可用
//!
//! ### Lint 改进
//! - `mismatched_lifetime_syntaxes` - 默认启用，检查生命周期语法一致性
//!
//! ## 迁移建议
//!
//! 1. 更新 Cargo.toml: `rust-version = "1.90"`, `edition = "2024"`
//! 2. 应用新的稳定 API 和 const 函数增强
//! 3. 检查并修复新 lint 警告
//!
//! 参考: [Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
"@

$newPattern189 = @"
//! # Rust 1.89 特性示例 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features.rs`
//!
//! ## 版本历史说明
//!
//! 本文件展示 Rust 1.89 版本的特性，当前项目已升级到 Rust 1.92.0。
//!
//! ### Rust 1.92.0 主要改进
//!
//! - **语言特性**: MaybeUninit 文档化、联合体原始引用、关联项多边界等
//! - **标准库**: NonZero::div_ceil、rotate_right、Location::file_as_c_str
//! - **性能优化**: 迭代器方法特化、改进的编译优化
//!
//! ### 迁移建议
//!
//! 1. 更新 Cargo.toml: `rust-version = "1.92"`
//! 2. 参考对应模块的 `rust_192_features.rs` 了解最新特性
//! 3. 查看 `docs/RUST_192_*_IMPROVEMENTS.md` 了解完整改进
//!
//! 参考:
//! - [Rust 1.92.0 Release Notes](https://releases.rs/docs/1.92.0/)
//! - [历史版本: Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
"@

# 查找所有 rust_189_*.rs 文件
$files189 = Get-ChildItem -Path "crates" -Recurse -Filter "rust_189_*.rs" | Where-Object { $_.FullName -notmatch "\\target\\" }

$updatedCount = 0
foreach ($file in $files189) {
    try {
        $content = Get-Content $file.FullName -Raw -Encoding UTF8

        # 检查是否包含旧模式
        if ($content -match "⚠️ \*\*注意\*\*.*Rust 1\.90\.0 Release Notes") {
            $content = $content -replace [regex]::Escape($oldPattern189), $newPattern189
            Set-Content -Path $file.FullName -Value $content -Encoding UTF8 -NoNewline
            Write-Host "已更新: $($file.FullName)" -ForegroundColor Yellow
            $updatedCount++
        }
    } catch {
        Write-Host "错误处理文件 $($file.FullName): $_" -ForegroundColor Red
    }
}

Write-Host "`n更新完成! 共更新 $updatedCount 个文件" -ForegroundColor Green
Write-Host "提示: 请手动检查更新后的文件，确保内容正确" -ForegroundColor Cyan
