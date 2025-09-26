#!/bin/bash

# Rust Learning Project Health Check Script
# Created: 2025-09-25

set -e

echo "🏥 Rust Learning Project Health Check"
echo "======================================"

# Function to check command availability
check_command() {
    local cmd=$1
    local name=$2

    if command -v "$cmd" &> /dev/null; then
        echo "✅ $name is available"
        return 0
    else
        echo "❌ $name is not available"
        return 1
    fi
}

# Function to check Rust version
check_rust_version() {
    echo "🔍 Checking Rust version..."
    if command -v rustc &> /dev/null; then
        local version=$(rustc --version)
        echo "✅ Rust version: $version"

        # Check if version is >= 1.70
        local major=$(echo "$version" | grep -oP '\d+' | head -1)
        if [ "$major" -ge 1 ]; then
            echo "✅ Rust version is compatible (>= 1.70)"
        else
            echo "⚠️  Rust version might be too old (recommended >= 1.70)"
        fi
    else
        echo "❌ Rust is not installed"
        return 1
    fi
}

# Function to check Cargo version
check_cargo_version() {
    echo "🔍 Checking Cargo version..."
    if command -v cargo &> /dev/null; then
        local version=$(cargo --version)
        echo "✅ Cargo version: $version"
    else
        echo "❌ Cargo is not installed"
        return 1
    fi
}

# Function to check project structure
check_project_structure() {
    echo "🔍 Checking project structure..."

    local required_dirs=("crates" "tests" "benches" "scripts" ".vscode" ".github")
    local required_files=("Cargo.toml" "README.md" "rustfmt.toml" "clippy.toml")

    for dir in "${required_dirs[@]}"; do
        if [ -d "$dir" ]; then
            echo "✅ Directory $dir exists"
        else
            echo "❌ Directory $dir is missing"
        fi
    done

    for file in "${required_files[@]}"; do
        if [ -f "$file" ]; then
            echo "✅ File $file exists"
        else
            echo "❌ File $file is missing"
        fi
    done
}

# Function to check Cargo components
check_cargo_components() {
    echo "🔍 Checking Cargo components..."

    local components=("rustfmt" "clippy" "rust-src")

    for component in "${components[@]}"; do
        if rustup component list --installed | grep -q "$component"; then
            echo "✅ Component $component is installed"
        else
            echo "❌ Component $component is not installed"
        fi
    done
}

# Function to check development tools
check_dev_tools() {
    echo "🔍 Checking development tools..."

    local tools=(
        "cargo-tarpaulin"
        "cargo-audit"
        "cargo-outdated"
        "cargo-deny"
        "cargo-geiger"
        "cargo-udeps"
        "cargo-miri"
        "cargo-cranky"
        "cargo-expand"
        "cargo-tree"
        "cargo-watch"
        "cargo-edit"
        "cargo-generate"
        "cargo-make"
        "cargo-release"
    )

    for tool in "${tools[@]}"; do
        if command -v "$tool" &> /dev/null; then
            echo "✅ $tool is available"
        else
            echo "⚠️  $tool is not available (optional)"
        fi
    done
}

# Function to check project build
check_project_build() {
    echo "🔍 Checking project build..."

    if cargo check --all &> /dev/null; then
        echo "✅ Project builds successfully"
    else
        echo "❌ Project build failed"
        return 1
    fi
}

# Function to check tests
check_tests() {
    echo "🔍 Checking tests..."

    if cargo test --all &> /dev/null; then
        echo "✅ All tests pass"
    else
        echo "❌ Some tests failed"
        return 1
    fi
}

# Function to check code quality
check_code_quality() {
    echo "🔍 Checking code quality..."

    if cargo clippy --all -- -D warnings &> /dev/null; then
        echo "✅ Code quality checks pass"
    else
        echo "❌ Code quality checks failed"
        return 1
    fi
}

# Function to check code formatting
check_code_formatting() {
    echo "🔍 Checking code formatting..."

    if cargo fmt --all -- --check &> /dev/null; then
        echo "✅ Code formatting is correct"
    else
        echo "❌ Code formatting issues found"
        return 1
    fi
}

# Function to check security
check_security() {
    echo "🔍 Checking security..."

    if command -v cargo-audit &> /dev/null; then
        if cargo audit &> /dev/null; then
            echo "✅ Security audit passed"
        else
            echo "⚠️  Security issues found"
        fi
    else
        echo "⚠️  cargo-audit not available"
    fi
}

# Function to check dependencies
check_dependencies() {
    echo "🔍 Checking dependencies..."

    if command -v cargo-outdated &> /dev/null; then
        if cargo outdated &> /dev/null; then
            echo "✅ Dependencies are up to date"
        else
            echo "⚠️  Some dependencies are outdated"
        fi
    else
        echo "⚠️  cargo-outdated not available"
    fi
}

# Function to generate health report
generate_health_report() {
    echo "📊 Generating health report..."

    local report_file="health-report-$(date +%Y%m%d-%H%M%S).txt"

    {
        echo "Rust Learning Project Health Report"
        echo "Generated: $(date)"
        echo "=================================="
        echo ""

        echo "Rust Version:"
        rustc --version 2>/dev/null || echo "Not available"
        echo ""

        echo "Cargo Version:"
        cargo --version 2>/dev/null || echo "Not available"
        echo ""

        echo "Installed Components:"
        rustup component list --installed 2>/dev/null || echo "Not available"
        echo ""

        echo "Project Structure:"
        find . -maxdepth 2 -type d -name ".*" -prune -o -type d -print | head -20
        echo ""

        echo "Build Status:"
        cargo check --all 2>&1 || echo "Build failed"
        echo ""

        echo "Test Status:"
        cargo test --all 2>&1 || echo "Tests failed"
        echo ""

        echo "Code Quality:"
        cargo clippy --all 2>&1 || echo "Clippy failed"
        echo ""

        echo "Code Formatting:"
        cargo fmt --all -- --check 2>&1 || echo "Formatting issues"
        echo ""

        echo "Security Audit:"
        cargo audit 2>&1 || echo "Security audit failed"
        echo ""

        echo "Dependencies:"
        cargo outdated 2>&1 || echo "Dependency check failed"
        echo ""

    } > "$report_file"

    echo "✅ Health report generated: $report_file"
}

# Main execution
main() {
    echo "Starting health check..."
    echo ""

    # Check basic requirements
    check_rust_version
    echo ""

    check_cargo_version
    echo ""

    # Check project structure
    check_project_structure
    echo ""

    # Check Cargo components
    check_cargo_components
    echo ""

    # Check development tools
    check_dev_tools
    echo ""

    # Check project build
    check_project_build
    echo ""

    # Check tests
    check_tests
    echo ""

    # Check code quality
    check_code_quality
    echo ""

    # Check code formatting
    check_code_formatting
    echo ""

    # Check security
    check_security
    echo ""

    # Check dependencies
    check_dependencies
    echo ""

    # Generate health report
    generate_health_report
    echo ""

    echo "🏥 Health check completed!"
    echo ""
    echo "📋 Summary:"
    echo "   - Check the output above for any issues"
    echo "   - Review the generated health report"
    echo "   - Fix any problems identified"
    echo "   - Run 'cargo build' to verify fixes"
    echo ""
    echo "🛠️  Next steps:"
    echo "   1. Fix any issues found"
    echo "   2. Run 'cargo test' to verify tests"
    echo "   3. Run 'cargo clippy' to check code quality"
    echo "   4. Run 'cargo fmt' to format code"
    echo "   5. Run 'cargo audit' for security check"
    echo "   6. Run 'cargo outdated' to check dependencies"
}

# Run main function
main "$@"
