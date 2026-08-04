# Rust Learning Project Development Setup Script (PowerShell)
# Created: 2025-09-25

param(
    [switch]$Force,
    [switch]$Verbose
)

$ErrorActionPreference = "Stop"

Write-Host "🚀 Setting up Rust Learning Project development environment..." -ForegroundColor Green

# Check if Rust is installed
try {
    $rustVersion = rustc --version
    Write-Host "✅ Rust is installed: $rustVersion" -ForegroundColor Green
}
catch {
    Write-Host "❌ Rust is not installed. Please install Rust first." -ForegroundColor Red
    Write-Host "   Visit: https://rustup.rs/" -ForegroundColor Yellow
    exit 1
}

# Check if Cargo is installed
try {
    $cargoVersion = cargo --version
    Write-Host "✅ Cargo is installed: $cargoVersion" -ForegroundColor Green
}
catch {
    Write-Host "❌ Cargo is not installed. Please install Cargo first." -ForegroundColor Red
    exit 1
}

# Install Rust components
Write-Host "📦 Installing Rust components..." -ForegroundColor Blue
rustup component add rustfmt clippy rust-src

# Install development tools
Write-Host "🔧 Installing development tools..." -ForegroundColor Blue

# Install cargo tools
$cargoTools = @(
    "cargo-tarpaulin",  # Code coverage
    "cargo-audit",      # Security audit
    "cargo-outdated",   # Dependency updates
    "cargo-deny",       # Dependency analysis
    "cargo-geiger",     # Unsafe code analysis
    "cargo-udeps",      # Unused dependencies
    "cargo-miri",       # Miri interpreter
    "cargo-cranky",     # Additional lints
    "cargo-expand",     # Macro expansion
    "cargo-tree",       # Dependency tree
    "cargo-watch",      # File watching
    "cargo-edit",       # Cargo subcommands
    "cargo-generate",   # Project generation
    "cargo-make",       # Task runner
    "cargo-release"     # Release automation
)

foreach ($tool in $cargoTools) {
    try {
        Write-Host "Installing $tool..." -ForegroundColor Yellow
        cargo install $tool
        Write-Host "✅ $tool installed successfully" -ForegroundColor Green
    }
    catch {
        Write-Host "⚠️  Failed to install $tool" -ForegroundColor Yellow
    }
}

# Install additional tools
$additionalTools = @(
    "ripgrep",          # Fast grep
    "fd",               # Fast find
    "bat",              # Better cat
    "exa",              # Better ls
    "procs",            # Better ps
    "dust",             # Better du
    "tokei",            # Code statistics
    "hyperfine",        # Benchmark tool
    "flamegraph"        # Performance profiling
)

foreach ($tool in $additionalTools) {
    try {
        Write-Host "Installing $tool..." -ForegroundColor Yellow
        cargo install $tool
        Write-Host "✅ $tool installed successfully" -ForegroundColor Green
    }
    catch {
        Write-Host "⚠️  Failed to install $tool" -ForegroundColor Yellow
    }
}

Write-Host "✅ Development tools installation completed!" -ForegroundColor Green

# Verify installation
Write-Host "🔍 Verifying installation..." -ForegroundColor Blue
cargo --version
rustc --version
rustfmt --version
clippy-driver --version

Write-Host "🎉 Development environment setup complete!" -ForegroundColor Green
Write-Host ""
Write-Host "📚 Next steps:" -ForegroundColor Cyan
Write-Host "   1. Run 'cargo build' to build the project" -ForegroundColor White
Write-Host "   2. Run 'cargo test' to run tests" -ForegroundColor White
Write-Host "   3. Run 'cargo clippy' to check code quality" -ForegroundColor White
Write-Host "   4. Run 'cargo fmt' to format code" -ForegroundColor White
Write-Host "   5. Run 'cargo tarpaulin' for code coverage" -ForegroundColor White
Write-Host "   6. Run 'cargo audit' for security audit" -ForegroundColor White
Write-Host ""
Write-Host "🛠️  Available commands:" -ForegroundColor Cyan
Write-Host "   cargo build          - Build the project" -ForegroundColor White
Write-Host "   cargo test           - Run tests" -ForegroundColor White
Write-Host "   cargo clippy         - Run clippy lints" -ForegroundColor White
Write-Host "   cargo fmt            - Format code" -ForegroundColor White
Write-Host "   cargo doc            - Generate documentation" -ForegroundColor White
Write-Host "   cargo bench          - Run benchmarks" -ForegroundColor White
Write-Host "   cargo tarpaulin      - Code coverage" -ForegroundColor White
Write-Host "   cargo audit          - Security audit" -ForegroundColor White
Write-Host "   cargo outdated       - Check outdated dependencies" -ForegroundColor White
Write-Host "   cargo deny           - Dependency analysis" -ForegroundColor White
Write-Host "   cargo geiger         - Unsafe code analysis" -ForegroundColor White
Write-Host "   cargo udeps          - Unused dependencies" -ForegroundColor White
Write-Host "   cargo miri           - Miri interpreter" -ForegroundColor White
Write-Host "   cargo cranky         - Additional lints" -ForegroundColor White
Write-Host "   cargo expand         - Macro expansion" -ForegroundColor White
Write-Host "   cargo tree           - Dependency tree" -ForegroundColor White
Write-Host "   cargo watch          - File watching" -ForegroundColor White
Write-Host "   cargo edit           - Cargo subcommands" -ForegroundColor White
Write-Host "   cargo generate       - Project generation" -ForegroundColor White
Write-Host "   cargo make           - Task runner" -ForegroundColor White
Write-Host "   cargo release        - Release automation" -ForegroundColor White
Write-Host ""
Write-Host "📖 For more information, visit: https://doc.rust-lang.org/cargo/" -ForegroundColor Yellow
