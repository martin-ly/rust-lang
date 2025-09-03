@echo off
REM Rust 1.89 控制流与函数特性研究项目构建脚本 (Windows)
REM 支持多平台构建和测试

setlocal enabledelayedexpansion

REM 设置错误处理
set "EXIT_CODE=0"

REM 颜色定义 (Windows 10+ 支持)
if "%TERM%"=="xterm-256color" (
    set "RED=[91m"
    set "GREEN=[92m"
    set "YELLOW=[93m"
    set "BLUE=[94m"
    set "NC=[0m"
) else (
    set "RED="
    set "GREEN="
    set "YELLOW="
    set "BLUE="
    set "NC="
)

REM 日志函数
:log_info
echo %BLUE%[INFO]%NC% %~1
goto :eof

:log_success
echo %GREEN%[SUCCESS]%NC% %~1
goto :eof

:log_warning
echo %YELLOW%[WARNING]%NC% %~1
goto :eof

:log_error
echo %RED%[ERROR]%NC% %~1
goto :eof

REM 检查Rust版本
:check_rust_version
call :log_info "检查Rust版本..."
rustc --version >nul 2>&1
if errorlevel 1 (
    call :log_error "Rust未安装，请先安装Rust"
    set "EXIT_CODE=1"
    goto :end
)

for /f "tokens=2" %%i in ('rustc --version') do set "RUST_VERSION=%%i"
call :log_info "当前Rust版本: %RUST_VERSION%"
call :log_info "需要Rust版本: 1.89.0"

REM 简单的版本检查
if "%RUST_VERSION%"=="1.89.0" (
    call :log_success "Rust版本符合要求"
) else (
    call :log_warning "Rust版本可能过低，建议升级到1.89.0或更高版本"
)
goto :eof

REM 安装依赖
:install_dependencies
call :log_info "安装项目依赖..."

REM 安装rustup组件
rustup component add rustfmt clippy
if errorlevel 1 (
    call :log_error "安装rustup组件失败"
    set "EXIT_CODE=1"
    goto :end
)

REM 安装cargo工具
cargo install cargo-audit
cargo install cargo-tarpaulin
cargo install cargo-criterion

call :log_success "依赖安装完成"
goto :eof

REM 代码格式化
:format_code
call :log_info "格式化代码..."
cargo fmt --all -- --check
if errorlevel 1 (
    call :log_error "代码格式化检查失败"
    set "EXIT_CODE=1"
    goto :end
)
call :log_success "代码格式化检查完成"
goto :eof

REM 代码检查
:check_code
call :log_info "检查代码..."
cargo clippy --all-targets --all-features -- -D warnings
if errorlevel 1 (
    call :log_error "代码检查失败"
    set "EXIT_CODE=1"
    goto :end
)
call :log_success "代码检查完成"
goto :eof

REM 安全审计
:audit_code
call :log_info "安全审计..."
cargo audit
if errorlevel 1 (
    call :log_warning "安全审计发现问题，请检查"
)
call :log_success "安全审计完成"
goto :eof

REM 构建项目
:build_project
set "PROFILE=%~1"
if "%PROFILE%"=="" set "PROFILE=debug"

call :log_info "构建项目 (profile: %PROFILE%)..."

if "%PROFILE%"=="release" (
    cargo build --release --verbose
) else (
    cargo build --verbose
)

if errorlevel 1 (
    call :log_error "项目构建失败"
    set "EXIT_CODE=1"
    goto :end
)

call :log_success "项目构建完成"
goto :eof

REM 运行测试
:run_tests
set "FEATURES=%~1"
call :log_info "运行测试..."

if not "%FEATURES%"=="" (
    cargo test --features "%FEATURES%" --verbose
) else (
    cargo test --verbose
)

if errorlevel 1 (
    call :log_error "测试失败"
    set "EXIT_CODE=1"
    goto :end
)

call :log_success "测试完成"
goto :eof

REM 运行基准测试
:run_benchmarks
call :log_info "运行基准测试..."
cargo criterion --message-format=json
if errorlevel 1 (
    call :log_error "基准测试失败"
    set "EXIT_CODE=1"
    goto :end
)
call :log_success "基准测试完成"
goto :eof

REM 生成文档
:generate_docs
call :log_info "生成文档..."

REM 生成公共API文档
cargo doc --no-deps --all-features
if errorlevel 1 (
    call :log_error "生成公共API文档失败"
    set "EXIT_CODE=1"
    goto :end
)

REM 生成私有API文档
cargo doc --no-deps --document-private-items --all-features
if errorlevel 1 (
    call :log_error "生成私有API文档失败"
    set "EXIT_CODE=1"
    goto :end
)

call :log_success "文档生成完成"
call :log_info "文档位置: target\doc"
goto :eof

REM 代码覆盖率
:run_coverage
call :log_info "运行代码覆盖率测试..."
cargo tarpaulin --out Html --output-dir coverage
if errorlevel 1 (
    call :log_error "代码覆盖率测试失败"
    set "EXIT_CODE=1"
    goto :end
)
call :log_success "代码覆盖率测试完成"
call :log_info "覆盖率报告位置: coverage"
goto :eof

REM 清理构建文件
:clean_build
call :log_info "清理构建文件..."
cargo clean
call :log_success "清理完成"
goto :eof

REM 显示帮助信息
:show_help
echo Rust 1.89 控制流与函数特性研究项目构建脚本 (Windows)
echo.
echo 用法: %~nx0 [选项] [命令]
echo.
echo 选项:
echo   -h, --help     显示此帮助信息
echo   -v, --verbose  详细输出
echo   -f, --features 指定特性 (例如: async,generics,performance)
echo.
echo 命令:
echo   check          检查代码 (格式化 + clippy + 审计)
echo   build          构建项目
echo   test           运行测试
echo   bench          运行基准测试
echo   doc            生成文档
echo   coverage       运行代码覆盖率测试
echo   clean          清理构建文件
echo   all            执行所有步骤
echo.
echo 示例:
echo   %~nx0 check                    # 检查代码
echo   %~nx0 build release            # 发布模式构建
echo   %~nx0 test async,generics      # 运行特定特性的测试
echo   %~nx0 all                      # 执行所有步骤
goto :eof

REM 主函数
:main
set "VERBOSE=false"
set "FEATURES="
set "COMMAND="
set "BUILD_PROFILE="

REM 解析命令行参数
:parse_args
if "%~1"=="" goto :execute_command

if "%~1"=="-h" goto :show_help
if "%~1"=="--help" goto :show_help
if "%~1"=="-v" goto :set_verbose
if "%~1"=="--verbose" goto :set_verbose
if "%~1"=="-f" goto :set_features
if "%~1"=="--features" goto :set_features

if "%~1"=="check" goto :set_command
if "%~1"=="build" goto :set_command
if "%~1"=="test" goto :set_command
if "%~1"=="bench" goto :set_command
if "%~1"=="doc" goto :set_command
if "%~1"=="coverage" goto :set_command
if "%~1"=="clean" goto :set_command
if "%~1"=="all" goto :set_command

if "%~1"=="debug" goto :set_build_profile
if "%~1"=="release" goto :set_build_profile

call :log_error "未知参数: %~1"
call :show_help
set "EXIT_CODE=1"
goto :end

:set_verbose
set "VERBOSE=true"
shift
goto :parse_args

:set_features
set "FEATURES=%~2"
shift
shift
goto :parse_args

:set_command
set "COMMAND=%~1"
shift
goto :parse_args

:set_build_profile
if "%COMMAND%"=="build" set "BUILD_PROFILE=%~1"
shift
goto :parse_args

:execute_command
REM 如果没有指定命令，显示帮助
if "%COMMAND%"=="" goto :show_help

REM 设置详细输出
if "%VERBOSE%"=="true" (
    set "CARGO_VERBOSE=--verbose"
) else (
    set "CARGO_VERBOSE="
)

REM 检查Rust版本
call :check_rust_version
if %EXIT_CODE% neq 0 goto :end

REM 执行命令
if "%COMMAND%"=="check" goto :execute_check
if "%COMMAND%"=="build" goto :execute_build
if "%COMMAND%"=="test" goto :execute_test
if "%COMMAND%"=="bench" goto :execute_bench
if "%COMMAND%"=="doc" goto :execute_doc
if "%COMMAND%"=="coverage" goto :execute_coverage
if "%COMMAND%"=="clean" goto :execute_clean
if "%COMMAND%"=="all" goto :execute_all

call :log_error "未知命令: %COMMAND%"
set "EXIT_CODE=1"
goto :end

:execute_check
call :format_code
call :check_code
call :audit_code
goto :end

:execute_build
call :build_project "%BUILD_PROFILE%"
goto :end

:execute_test
call :run_tests "%FEATURES%"
goto :end

:execute_bench
call :run_benchmarks
goto :end

:execute_doc
call :generate_docs
goto :end

:execute_coverage
call :run_coverage
goto :end

:execute_clean
call :clean_build
goto :end

:execute_all
call :log_info "执行所有步骤..."
call :install_dependencies
call :format_code
call :check_code
call :audit_code
call :build_project "release"
call :run_tests "%FEATURES%"
call :run_benchmarks
call :generate_docs
call :run_coverage
call :log_success "所有步骤执行完成！"
goto :end

:end
if %EXIT_CODE% equ 0 (
    call :log_success "脚本执行成功"
) else (
    call :log_error "脚本执行失败 (退出码: %EXIT_CODE%)"
)
exit /b %EXIT_CODE%

REM 脚本入口点
if "%~f0"=="%~f1" goto :main
goto :eof
