#!/bin/bash

# Rust Learning Project Development Setup Script
# Created: 2025-09-25

set -e

echo "🚀 Setting up Rust Learning Project development environment..."

# Check if Rust is installed
if ! command -v rustc &> /dev/null; then
    echo "❌ Rust is not installed. Please install Rust first."
    echo "   Visit: https://rustup.rs/"
    exit 1
fi

echo "✅ Rust is installed: $(rustc --version)"

# Check if Cargo is installed
if ! command -v cargo &> /dev/null; then
    echo "❌ Cargo is not installed. Please install Cargo first."
    exit 1
fi

echo "✅ Cargo is installed: $(cargo --version)"

# Install Rust components
echo "📦 Installing Rust components..."
rustup component add rustfmt clippy rust-src

# Install development tools
echo "🔧 Installing development tools..."

# Install cargo tools
cargo install cargo-tarpaulin  # Code coverage
cargo install cargo-audit      # Security audit
cargo install cargo-outdated   # Dependency updates
cargo install cargo-deny       # Dependency analysis
cargo install cargo-geiger     # Unsafe code analysis
cargo install cargo-udeps      # Unused dependencies
cargo install cargo-miri       # Miri interpreter
cargo install cargo-cranky     # Additional lints
cargo install cargo-expand     # Macro expansion
cargo install cargo-tree       # Dependency tree
cargo install cargo-watch      # File watching
cargo install cargo-edit       # Cargo subcommands
cargo install cargo-generate   # Project generation
cargo install cargo-make       # Task runner
cargo install cargo-release    # Release automation

# Install additional tools
cargo install ripgrep          # Fast grep
cargo install fd               # Fast find
cargo install bat              # Better cat
cargo install exa              # Better ls
cargo install procs            # Better ps
cargo install dust             # Better du
cargo install tokei            # Code statistics
cargo install hyperfine        # Benchmark tool
cargo install flamegraph       # Performance profiling

echo "✅ Development tools installed successfully!"

# Verify installation
echo "🔍 Verifying installation..."
cargo --version
rustc --version
rustfmt --version
clippy-driver --version

echo "🎉 Development environment setup complete!"
echo ""
echo "📚 Next steps:"
echo "   1. Run 'cargo build' to build the project"
echo "   2. Run 'cargo test' to run tests"
echo "   3. Run 'cargo clippy' to check code quality"
echo "   4. Run 'cargo fmt' to format code"
echo "   5. Run 'cargo tarpaulin' for code coverage"
echo "   6. Run 'cargo audit' for security audit"
echo ""
echo "🛠️  Available commands:"
echo "   cargo build          - Build the project"
echo "   cargo test           - Run tests"
echo "   cargo clippy         - Run clippy lints"
echo "   cargo fmt            - Format code"
echo "   cargo doc            - Generate documentation"
echo "   cargo bench          - Run benchmarks"
echo "   cargo tarpaulin      - Code coverage"
echo "   cargo audit          - Security audit"
echo "   cargo outdated       - Check outdated dependencies"
echo "   cargo deny           - Dependency analysis"
echo "   cargo geiger         - Unsafe code analysis"
echo "   cargo udeps          - Unused dependencies"
echo "   cargo miri           - Miri interpreter"
echo "   cargo cranky         - Additional lints"
echo "   cargo expand         - Macro expansion"
echo "   cargo tree           - Dependency tree"
echo "   cargo watch          - File watching"
echo "   cargo edit           - Cargo subcommands"
echo "   cargo generate       - Project generation"
echo "   cargo make           - Task runner"
echo "   cargo release        - Release automation"
echo ""
echo "📖 For more information, visit: https://doc.rust-lang.org/cargo/"
