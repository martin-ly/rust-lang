#!/bin/bash

# Rust Learning Project Clean Script
# Created: 2025-09-25

set -e

echo "🧹 Rust Learning Project Clean Script"
echo "====================================="

# Function to clean build artifacts
clean_build_artifacts() {
    echo "🗑️  Cleaning build artifacts..."

    if [ -d "target" ]; then
        echo "   Removing target directory..."
        rm -rf target
        echo "   ✅ Target directory removed"
    else
        echo "   ✅ No target directory found"
    fi

    if [ -d "Cargo.lock" ]; then
        echo "   Removing Cargo.lock..."
        rm -f Cargo.lock
        echo "   ✅ Cargo.lock removed"
    else
        echo "   ✅ No Cargo.lock found"
    fi
}

# Function to clean documentation
clean_documentation() {
    echo "🗑️  Cleaning documentation..."

    if [ -d "target/doc" ]; then
        echo "   Removing documentation..."
        rm -rf target/doc
        echo "   ✅ Documentation removed"
    else
        echo "   ✅ No documentation found"
    fi
}

# Function to clean test artifacts
clean_test_artifacts() {
    echo "🗑️  Cleaning test artifacts..."

    # Remove test output files
    find . -name "*.test" -type f -delete 2>/dev/null || true
    find . -name "*.prof" -type f -delete 2>/dev/null || true
    find . -name "*.gcov" -type f -delete 2>/dev/null || true
    find . -name "*.gcda" -type f -delete 2>/dev/null || true
    find . -name "*.gcno" -type f -delete 2>/dev/null || true

    echo "   ✅ Test artifacts cleaned"
}

# Function to clean coverage reports
clean_coverage_reports() {
    echo "🗑️  Cleaning coverage reports..."

    # Remove coverage files
    find . -name "*.lcov" -type f -delete 2>/dev/null || true
    find . -name "*.info" -type f -delete 2>/dev/null || true
    find . -name "coverage" -type d -exec rm -rf {} + 2>/dev/null || true
    find . -name "tarpaulin-report.html" -type f -delete 2>/dev/null || true
    find . -name "tarpaulin-report.xml" -type f -delete 2>/dev/null || true

    echo "   ✅ Coverage reports cleaned"
}

# Function to clean benchmark results
clean_benchmark_results() {
    echo "🗑️  Cleaning benchmark results..."

    # Remove benchmark files
    find . -name "criterion" -type d -exec rm -rf {} + 2>/dev/null || true
    find . -name "*.bench" -type f -delete 2>/dev/null || true

    echo "   ✅ Benchmark results cleaned"
}

# Function to clean temporary files
clean_temporary_files() {
    echo "🗑️  Cleaning temporary files..."

    # Remove temporary files
    find . -name "*.tmp" -type f -delete 2>/dev/null || true
    find . -name "*.temp" -type f -delete 2>/dev/null || true
    find . -name "*.swp" -type f -delete 2>/dev/null || true
    find . -name "*.swo" -type f -delete 2>/dev/null || true
    find . -name "*~" -type f -delete 2>/dev/null || true
    find . -name ".#*" -type f -delete 2>/dev/null || true

    echo "   ✅ Temporary files cleaned"
}

# Function to clean log files
clean_log_files() {
    echo "🗑️  Cleaning log files..."

    # Remove log files
    find . -name "*.log" -type f -delete 2>/dev/null || true
    find . -name "*.out" -type f -delete 2>/dev/null || true
    find . -name "*.err" -type f -delete 2>/dev/null || true

    echo "   ✅ Log files cleaned"
}

# Function to clean backup files
clean_backup_files() {
    echo "🗑️  Cleaning backup files..."

    # Remove backup files
    find . -name "*.bak" -type f -delete 2>/dev/null || true
    find . -name "*.backup" -type f -delete 2>/dev/null || true
    find . -name "*.orig" -type f -delete 2>/dev/null || true

    echo "   ✅ Backup files cleaned"
}

# Function to clean IDE files
clean_ide_files() {
    echo "🗑️  Cleaning IDE files..."

    # Remove IDE-specific files
    find . -name ".DS_Store" -type f -delete 2>/dev/null || true
    find . -name "Thumbs.db" -type f -delete 2>/dev/null || true
    find . -name "*.suo" -type f -delete 2>/dev/null || true
    find . -name "*.user" -type f -delete 2>/dev/null || true
    find . -name "*.userosscache" -type f -delete 2>/dev/null || true
    find . -name "*.sln.docstates" -type f -delete 2>/dev/null || true

    echo "   ✅ IDE files cleaned"
}

# Function to clean cache files
clean_cache_files() {
    echo "🗑️  Cleaning cache files..."

    # Remove cache directories
    find . -name ".cache" -type d -exec rm -rf {} + 2>/dev/null || true
    find . -name "cache" -type d -exec rm -rf {} + 2>/dev/null || true
    find . -name ".tmp" -type d -exec rm -rf {} + 2>/dev/null || true
    find . -name "tmp" -type d -exec rm -rf {} + 2>/dev/null || true

    echo "   ✅ Cache files cleaned"
}

# Function to clean node_modules (if any)
clean_node_modules() {
    echo "🗑️  Cleaning node_modules..."

    if [ -d "node_modules" ]; then
        echo "   Removing node_modules..."
        rm -rf node_modules
        echo "   ✅ node_modules removed"
    else
        echo "   ✅ No node_modules found"
    fi
}

# Function to clean Python cache (if any)
clean_python_cache() {
    echo "🗑️  Cleaning Python cache..."

    # Remove Python cache files
    find . -name "__pycache__" -type d -exec rm -rf {} + 2>/dev/null || true
    find . -name "*.pyc" -type f -delete 2>/dev/null || true
    find . -name "*.pyo" -type f -delete 2>/dev/null || true
    find . -name "*.pyd" -type f -delete 2>/dev/null || true

    echo "   ✅ Python cache cleaned"
}

# Function to clean Git files (optional)
clean_git_files() {
    echo "🗑️  Cleaning Git files..."

    # Remove Git files (be careful with this)
    if [ -d ".git" ]; then
        echo "   ⚠️  .git directory found - skipping for safety"
        echo "   ✅ Git files preserved"
    else
        echo "   ✅ No .git directory found"
    fi
}

# Function to clean specific directories
clean_specific_directories() {
    echo "🗑️  Cleaning specific directories..."

    local dirs_to_clean=(
        "dist"
        "build"
        "out"
        "bin"
        "obj"
        "Debug"
        "Release"
        "x64"
        "x86"
        "ARM"
        "ARM64"
    )

    for dir in "${dirs_to_clean[@]}"; do
        if [ -d "$dir" ]; then
            echo "   Removing $dir directory..."
            rm -rf "$dir"
            echo "   ✅ $dir directory removed"
        else
            echo "   ✅ No $dir directory found"
        fi
    done
}

# Function to show disk usage
show_disk_usage() {
    echo "💾 Disk usage before cleaning:"
    du -sh . 2>/dev/null || echo "   Unable to calculate disk usage"

    echo ""
    echo "💾 Disk usage after cleaning:"
    du -sh . 2>/dev/null || echo "   Unable to calculate disk usage"
}

# Function to show what will be cleaned
show_cleanup_preview() {
    echo "🔍 Cleanup preview:"
    echo ""

    echo "   Build artifacts:"
    if [ -d "target" ]; then
        echo "     - target/ directory"
    fi
    if [ -f "Cargo.lock" ]; then
        echo "     - Cargo.lock file"
    fi

    echo "   Documentation:"
    if [ -d "target/doc" ]; then
        echo "     - target/doc/ directory"
    fi

    echo "   Test artifacts:"
    find . -name "*.test" -type f 2>/dev/null | head -5 | while read -r file; do
        echo "     - $file"
    done

    echo "   Coverage reports:"
    find . -name "*.lcov" -type f 2>/dev/null | head -5 | while read -r file; do
        echo "     - $file"
    done

    echo "   Benchmark results:"
    find . -name "criterion" -type d 2>/dev/null | head -5 | while read -r dir; do
        echo "     - $dir"
    done

    echo "   Temporary files:"
    find . -name "*.tmp" -type f 2>/dev/null | head -5 | while read -r file; do
        echo "     - $file"
    done

    echo "   Log files:"
    find . -name "*.log" -type f 2>/dev/null | head -5 | while read -r file; do
        echo "     - $file"
    done

    echo "   Backup files:"
    find . -name "*.bak" -type f 2>/dev/null | head -5 | while read -r file; do
        echo "     - $file"
    done

    echo "   IDE files:"
    find . -name ".DS_Store" -type f 2>/dev/null | head -5 | while read -r file; do
        echo "     - $file"
    done

    echo "   Cache files:"
    find . -name ".cache" -type d 2>/dev/null | head -5 | while read -r dir; do
        echo "     - $dir"
    done
}

# Main execution
main() {
    echo "Starting project cleanup..."
    echo ""

    # Show cleanup preview
    show_cleanup_preview
    echo ""

    # Ask for confirmation
    read -p "Do you want to proceed with cleanup? (y/N): " -n 1 -r
    echo ""

    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        echo "❌ Cleanup cancelled"
        exit 0
    fi

    echo ""
    echo "🧹 Starting cleanup process..."
    echo ""

    # Show disk usage before cleaning
    show_disk_usage
    echo ""

    # Clean various types of files
    clean_build_artifacts
    echo ""

    clean_documentation
    echo ""

    clean_test_artifacts
    echo ""

    clean_coverage_reports
    echo ""

    clean_benchmark_results
    echo ""

    clean_temporary_files
    echo ""

    clean_log_files
    echo ""

    clean_backup_files
    echo ""

    clean_ide_files
    echo ""

    clean_cache_files
    echo ""

    clean_node_modules
    echo ""

    clean_python_cache
    echo ""

    clean_git_files
    echo ""

    clean_specific_directories
    echo ""

    # Show disk usage after cleaning
    show_disk_usage
    echo ""

    echo "🎉 Project cleanup completed!"
    echo ""
    echo "📋 Summary:"
    echo "   - Build artifacts removed"
    echo "   - Documentation cleaned"
    echo "   - Test artifacts removed"
    echo "   - Coverage reports cleaned"
    echo "   - Benchmark results removed"
    echo "   - Temporary files cleaned"
    echo "   - Log files removed"
    echo "   - Backup files cleaned"
    echo "   - IDE files removed"
    echo "   - Cache files cleaned"
    echo "   - Specific directories cleaned"
    echo ""
    echo "🛠️  Next steps:"
    echo "   1. Run 'cargo build' to rebuild the project"
    echo "   2. Run 'cargo test' to run tests"
    echo "   3. Run 'cargo clippy' to check code quality"
    echo "   4. Run 'cargo fmt' to format code"
    echo "   5. Run 'cargo doc' to generate documentation"
    echo ""
    echo "💡 Tip: Run this script regularly to keep your project clean!"
}

# Run main function
main "$@"
