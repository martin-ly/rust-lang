#!/bin/bash

# Template Generator Script
# Created: 2025-09-25

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to print colored output
print_color() {
    local color=$1
    local message=$2
    echo -e "${color}${message}${NC}"
}

# Function to show usage
show_usage() {
    echo "Usage: $0 [OPTIONS]"
    echo ""
    echo "Generate a new Rust project from template"
    echo ""
    echo "Options:"
    echo "  -t, --template TEMPLATE    Template to use (basic-library, web-app, cli-app)"
    echo "  -n, --name NAME           Project name"
    echo "  -d, --description DESC    Project description"
    echo "  -a, --author AUTHOR       Author name"
    echo "  -r, --repository URL      Repository URL"
    echo "  -h, --homepage URL        Homepage URL"
    echo "  -k, --keywords KEYWORDS   Comma-separated keywords"
    echo "  -c, --categories CATS     Comma-separated categories"
    echo "  -o, --output DIR          Output directory (default: current directory)"
    echo "  --help                    Show this help message"
    echo ""
    echo "Examples:"
    echo "  $0 -t basic-library -n my-lib -d \"My awesome library\""
    echo "  $0 -t web-app -n my-web-app -d \"My web application\" -a \"John Doe\""
    echo "  $0 -t cli-app -n my-cli -d \"My CLI tool\" -r \"https://github.com/user/my-cli\""
}

# Default values
TEMPLATE=""
PROJECT_NAME=""
DESCRIPTION=""
AUTHOR=""
REPOSITORY_URL=""
HOMEPAGE_URL=""
KEYWORDS=""
CATEGORIES=""
OUTPUT_DIR="."

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -t|--template)
            TEMPLATE="$2"
            shift 2
            ;;
        -n|--name)
            PROJECT_NAME="$2"
            shift 2
            ;;
        -d|--description)
            DESCRIPTION="$2"
            shift 2
            ;;
        -a|--author)
            AUTHOR="$2"
            shift 2
            ;;
        -r|--repository)
            REPOSITORY_URL="$2"
            shift 2
            ;;
        -h|--homepage)
            HOMEPAGE_URL="$2"
            shift 2
            ;;
        -k|--keywords)
            KEYWORDS="$2"
            shift 2
            ;;
        -c|--categories)
            CATEGORIES="$2"
            shift 2
            ;;
        -o|--output)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --help)
            show_usage
            exit 0
            ;;
        *)
            print_color $RED "Unknown option: $1"
            show_usage
            exit 1
            ;;
    esac
done

# Validate required parameters
if [[ -z "$TEMPLATE" ]]; then
    print_color $RED "Error: Template is required"
    show_usage
    exit 1
fi

if [[ -z "$PROJECT_NAME" ]]; then
    print_color $RED "Error: Project name is required"
    show_usage
    exit 1
fi

if [[ -z "$DESCRIPTION" ]]; then
    print_color $RED "Error: Project description is required"
    show_usage
    exit 1
fi

# Validate template
case $TEMPLATE in
    basic-library|web-app|cli-app)
        ;;
    *)
        print_color $RED "Error: Invalid template '$TEMPLATE'"
        print_color $YELLOW "Available templates: basic-library, web-app, cli-app"
        exit 1
        ;;
esac

# Set default values
if [[ -z "$AUTHOR" ]]; then
    AUTHOR="Rust Developer"
fi

if [[ -z "$REPOSITORY_URL" ]]; then
    REPOSITORY_URL="https://github.com/user/$PROJECT_NAME"
fi

if [[ -z "$HOMEPAGE_URL" ]]; then
    HOMEPAGE_URL="$REPOSITORY_URL"
fi

if [[ -z "$KEYWORDS" ]]; then
    case $TEMPLATE in
        basic-library)
            KEYWORDS="library,rust,utils"
            ;;
        web-app)
            KEYWORDS="web,rust,api,server"
            ;;
        cli-app)
            KEYWORDS="cli,rust,command-line,tool"
            ;;
    esac
fi

if [[ -z "$CATEGORIES" ]]; then
    case $TEMPLATE in
        basic-library)
            CATEGORIES="library,development-tools"
            ;;
        web-app)
            CATEGORIES="web-programming,development-tools"
            ;;
        cli-app)
            CATEGORIES="command-line-utilities,development-tools"
            ;;
    esac
fi

# Create project directory
PROJECT_DIR="$OUTPUT_DIR/$PROJECT_NAME"
if [[ -d "$PROJECT_DIR" ]]; then
    print_color $RED "Error: Directory '$PROJECT_DIR' already exists"
    exit 1
fi

print_color $GREEN "Creating project '$PROJECT_NAME' from template '$TEMPLATE'..."

# Create project directory
mkdir -p "$PROJECT_DIR"

# Copy template files
TEMPLATE_DIR="templates/$TEMPLATE"
if [[ ! -d "$TEMPLATE_DIR" ]]; then
    print_color $RED "Error: Template directory '$TEMPLATE_DIR' not found"
    exit 1
fi

# Copy template files recursively
cp -r "$TEMPLATE_DIR"/* "$PROJECT_DIR/"

# Replace template variables
print_color $BLUE "Replacing template variables..."

# Convert project name to different formats
PROJECT_NAME_LOWER=$(echo "$PROJECT_NAME" | tr '[:upper:]' '[:lower:]')
PROJECT_NAME_UPPER=$(echo "$PROJECT_NAME" | tr '[:lower:]' '[:upper:]')
PROJECT_NAME_CAPITALIZED=$(echo "$PROJECT_NAME" | sed 's/.*/\u&/')
PROJECT_DESCRIPTION_LOWER=$(echo "$DESCRIPTION" | tr '[:upper:]' '[:lower:]')

# Replace variables in all files
find "$PROJECT_DIR" -type f -exec sed -i "s/{{project_name}}/$PROJECT_NAME_LOWER/g" {} \;
find "$PROJECT_DIR" -type f -exec sed -i "s/{{ProjectName}}/$PROJECT_NAME_CAPITALIZED/g" {} \;
find "$PROJECT_DIR" -type f -exec sed -i "s/{{PROJECT_NAME}}/$PROJECT_NAME_UPPER/g" {} \;
find "$PROJECT_DIR" -type f -exec sed -i "s/{{project_description}}/$DESCRIPTION/g" {} \;
find "$PROJECT_DIR" -type f -exec sed -i "s/{{project_description_lower}}/$PROJECT_DESCRIPTION_LOWER/g" {} \;
find "$PROJECT_DIR" -type f -exec sed -i "s/{{author_name}}/$AUTHOR/g" {} \;
find "$PROJECT_DIR" -type f -exec sed -i "s|{{repository_url}}|$REPOSITORY_URL|g" {} \;
find "$PROJECT_DIR" -type f -exec sed -i "s|{{homepage_url}}|$HOMEPAGE_URL|g" {} \;
find "$PROJECT_DIR" -type f -exec sed -i "s|{{documentation_url}}|$REPOSITORY_URL|g" {} \;
find "$PROJECT_DIR" -type f -exec sed -i "s/{{keywords}}/$KEYWORDS/g" {} \;
find "$PROJECT_DIR" -type f -exec sed -i "s/{{categories}}/$CATEGORIES/g" {} \;

# Create additional files
print_color $BLUE "Creating additional files..."

# Create README.md
cat > "$PROJECT_DIR/README.md" << EOF
# $PROJECT_NAME

$DESCRIPTION

## Features

- Feature 1
- Feature 2
- Feature 3

## Installation

\`\`\`bash
cargo install $PROJECT_NAME_LOWER
\`\`\`

## Usage

\`\`\`bash
$PROJECT_NAME_LOWER --help
\`\`\`

## Examples

\`\`\`rust
use $PROJECT_NAME_LOWER::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Your code here
    Ok(())
}
\`\`\`

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Author

$AUTHOR

## Repository

$REPOSITORY_URL
EOF

# Create LICENSE file
cat > "$PROJECT_DIR/LICENSE" << EOF
MIT License

Copyright (c) $(date +%Y) $AUTHOR

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
EOF

# Create .gitignore file
cat > "$PROJECT_DIR/.gitignore" << EOF
# Rust
target/
Cargo.lock
*.pdb

# IDE
.vscode/
.idea/
*.swp
*.swo
*~

# OS
.DS_Store
Thumbs.db

# Logs
*.log

# Runtime data
pids
*.pid
*.seed
*.pid.lock

# Coverage directory used by tools like istanbul
coverage/

# nyc test coverage
.nyc_output

# Grunt intermediate storage
.grunt

# Bower dependency directory
bower_components

# node-waf configuration
.lock-wscript

# Compiled binary addons
build/Release

# Dependency directories
node_modules/
jspm_packages/

# Optional npm cache directory
.npm

# Optional REPL history
.node_repl_history

# Output of 'npm pack'
*.tgz

# Yarn Integrity file
.yarn-integrity

# dotenv environment variables file
.env

# parcel-bundler cache
.cache
.parcel-cache

# next.js build output
.next

# nuxt.js build output
.nuxt

# vuepress build output
.vuepress/dist

# Serverless directories
.serverless

# FuseBox cache
.fusebox/

# DynamoDB Local files
.dynamodb/

# TernJS port file
.tern-port
EOF

# Create .editorconfig file
cat > "$PROJECT_DIR/.editorconfig" << EOF
root = true

[*]
charset = utf-8
end_of_line = lf
insert_final_newline = true
trim_trailing_whitespace = true
indent_style = space
indent_size = 4

[*.{rs,toml}]
indent_size = 4

[*.md]
trim_trailing_whitespace = false

[*.{yml,yaml}]
indent_size = 2
EOF

# Create rustfmt.toml
cat > "$PROJECT_DIR/rustfmt.toml" << EOF
# Rustfmt configuration for $PROJECT_NAME
max_width = 100
tab_spaces = 4
newline_style = "Unix"
use_field_init_shorthand = true
use_try_shorthand = true
trailing_comma = "Vertical"
trailing_semicolon = true
trailing_whitespace = "Always"
format_strings = true
format_code_in_doc_comments = true
format_macro_matchers = true
format_macro_bodies = true
format_generated_files = false
imports_granularity = "Module"
imports_layout = "Mixed"
imports_sort = "Preserve"
use_unicode = true
use_lower_hex = true
use_scientific_notation = true
EOF

# Create clippy.toml
cat > "$PROJECT_DIR/clippy.toml" << EOF
# Clippy configuration for $PROJECT_NAME
allow = [
    "clippy::too_many_arguments",
    "clippy::needless_pass_by_value",
    "clippy::missing_errors_doc",
    "clippy::missing_panics_doc",
]

deny = [
    "clippy::all",
    "clippy::pedantic",
    "clippy::nursery",
    "clippy::cargo",
]

warn = [
    "clippy::perf",
    "clippy::style",
    "clippy::correctness",
    "clippy::suspicious",
]

max_args = 7
max_complexity = 10
max_lines_per_function = 50
max_fields = 8
max_variants = 10
max_generics = 5
max_lifetimes = 3
max_trait_bounds = 5
max_type_params = 5
max_const_params = 5
max_associated_types = 5
max_associated_constants = 5
max_associated_functions = 5
max_methods = 20
EOF

# Initialize git repository
print_color $BLUE "Initializing git repository..."
cd "$PROJECT_DIR"
git init
git add .
git commit -m "Initial commit: $DESCRIPTION"

# Show success message
print_color $GREEN "Project '$PROJECT_NAME' created successfully!"
echo ""
print_color $YELLOW "Project directory: $PROJECT_DIR"
echo ""
print_color $BLUE "Next steps:"
echo "  1. cd $PROJECT_DIR"
echo "  2. cargo build"
echo "  3. cargo test"
echo "  4. cargo run"
echo "  5. cargo doc --open"
echo ""
print_color $GREEN "Happy coding! 🦀"
