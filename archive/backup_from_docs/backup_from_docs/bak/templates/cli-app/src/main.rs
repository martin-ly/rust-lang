//! {{project_description}}
//!
//! A command-line application built with Clap and Rust.

use clap::{Parser, Subcommand};
use colored::*;
use std::path::PathBuf;
use tracing::{debug, error, info, warn};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

/// {{project_description}}
#[derive(Parser)]
#[command(
    name = "{{project_name}}",
    about = "{{project_description}}",
    version = env!("CARGO_PKG_VERSION"),
    author = "{{author_name}}"
)]
pub struct Cli {
    /// Configuration file path
    #[arg(short, long, value_name = "FILE")]
    pub config: Option<PathBuf>,

    /// Verbose output
    #[arg(short, long, action = clap::ArgAction::Count)]
    pub verbose: u8,

    /// Quiet mode
    #[arg(short, long)]
    pub quiet: bool,

    /// Command to run
    #[command(subcommand)]
    pub command: Commands,
}

/// Available commands
#[derive(Subcommand)]
pub enum Commands {
    /// Process files
    Process {
        /// Input file or directory
        #[arg(short, long, value_name = "PATH")]
        input: PathBuf,

        /// Output file or directory
        #[arg(short, long, value_name = "PATH")]
        output: Option<PathBuf>,

        /// Pattern to match files
        #[arg(short, long, value_name = "PATTERN")]
        pattern: Option<String>,

        /// Recursive processing
        #[arg(short, long)]
        recursive: bool,
    },

    /// Generate report
    Report {
        /// Output format
        #[arg(short, long, value_enum, default_value = "json")]
        format: OutputFormat,

        /// Include detailed information
        #[arg(short, long)]
        detailed: bool,
    },

    /// Validate configuration
    Validate {
        /// Configuration file to validate
        #[arg(value_name = "FILE")]
        config: PathBuf,
    },

    /// Show version information
    Version,
}

/// Output format options
#[derive(clap::ValueEnum, Clone)]
pub enum OutputFormat {
    Json,
    Yaml,
    Csv,
    Table,
}

/// Application configuration
#[derive(Debug, Clone)]
pub struct AppConfig {
    /// Verbose level
    pub verbose: u8,

    /// Quiet mode
    pub quiet: bool,

    /// Configuration file path
    pub config_path: Option<PathBuf>,
}

impl Default for AppConfig {
    fn default() -> Self {
        Self {
            verbose: 0,
            quiet: false,
            config_path: None,
        }
    }
}

/// Application context
pub struct App {
    config: AppConfig,
}

impl App {
    /// Create a new application instance
    pub fn new(config: AppConfig) -> Self {
        Self { config }
    }

    /// Run the application
    pub async fn run(&self, cli: Cli) -> anyhow::Result<()> {
        info!("Starting {{project_name}} v{}", env!("CARGO_PKG_VERSION"));

        match cli.command {
            Commands::Process {
                input,
                output,
                pattern,
                recursive,
            } => {
                self.process_files(input, output, pattern, recursive)
                    .await?;
            }

            Commands::Report { format, detailed } => {
                self.generate_report(format, detailed).await?;
            }

            Commands::Validate { config } => {
                self.validate_config(config).await?;
            }

            Commands::Version => {
                self.show_version().await?;
            }
        }

        Ok(())
    }

    /// Process files
    async fn process_files(
        &self,
        input: PathBuf,
        output: Option<PathBuf>,
        pattern: Option<String>,
        recursive: bool,
    ) -> anyhow::Result<()> {
        if !self.config.quiet {
            println!("{}", "Processing files...".green().bold());
        }

        debug!("Input path: {:?}", input);
        debug!("Output path: {:?}", output);
        debug!("Pattern: {:?}", pattern);
        debug!("Recursive: {}", recursive);

        if !input.exists() {
            return Err(anyhow::anyhow!("Input path does not exist: {:?}", input));
        }

        let output_path = output.unwrap_or_else(|| {
            if input.is_file() {
                input.with_extension("processed")
            } else {
                input.join("processed")
            }
        });

        if !self.config.quiet {
            println!("  Input: {}", input.display().to_string().cyan());
            println!("  Output: {}", output_path.display().to_string().cyan());

            if let Some(pattern) = &pattern {
                println!("  Pattern: {}", pattern.yellow());
            }

            if recursive {
                println!("  Mode: {}", "Recursive".blue());
            }
        }

        // Simulate file processing
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

        if !self.config.quiet {
            println!("{}", "Processing completed successfully!".green().bold());
        }

        Ok(())
    }

    /// Generate report
    async fn generate_report(&self, format: OutputFormat, detailed: bool) -> anyhow::Result<()> {
        if !self.config.quiet {
            println!("{}", "Generating report...".green().bold());
        }

        debug!("Format: {:?}", format);
        debug!("Detailed: {}", detailed);

        let report_data = serde_json::json!({
            "application": "{{project_name}}",
            "version": env!("CARGO_PKG_VERSION"),
            "timestamp": chrono::Utc::now().to_rfc3339(),
            "detailed": detailed,
            "statistics": {
                "processed_files": 42,
                "errors": 0,
                "warnings": 3,
                "duration_ms": 1500
            }
        });

        let output = match format {
            OutputFormat::Json => serde_json::to_string_pretty(&report_data)?,
            OutputFormat::Yaml => serde_yaml::to_string(&report_data)?,
            OutputFormat::Csv => "format,value\njson,42\nyaml,0\ncsv,3\ntable,1500".to_string(),
            OutputFormat::Table => {
                format!(
                    "Application: {{project_name}}\nVersion: {}\nProcessed Files: 42\nErrors: 0\nWarnings: 3\nDuration: 1500ms",
                    env!("CARGO_PKG_VERSION")
                )
            }
        };

        if !self.config.quiet {
            println!("{}", "Report generated:".green().bold());
            println!("{}", output);
        } else {
            print!("{}", output);
        }

        Ok(())
    }

    /// Validate configuration
    async fn validate_config(&self, config: PathBuf) -> anyhow::Result<()> {
        if !self.config.quiet {
            println!("{}", "Validating configuration...".green().bold());
        }

        debug!("Config path: {:?}", config);

        if !config.exists() {
            return Err(anyhow::anyhow!(
                "Configuration file does not exist: {:?}",
                config
            ));
        }

        if !config.is_file() {
            return Err(anyhow::anyhow!("Path is not a file: {:?}", config));
        }

        // Simulate configuration validation
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

        if !self.config.quiet {
            println!("{}", "Configuration is valid!".green().bold());
        }

        Ok(())
    }

    /// Show version information
    async fn show_version(&self) -> anyhow::Result<()> {
        println!("{{project_name}} v{}", env!("CARGO_PKG_VERSION"));
        println!("Built with Rust {}", env!("RUSTC_CHANNEL"));
        println!("Author: {{author_name}}");
        println!("Repository: {{repository_url}}");
        println!("Homepage: {{homepage_url}}");

        Ok(())
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // Parse command line arguments
    let cli = Cli::parse();

    // Initialize tracing
    let filter = if cli.quiet {
        "error"
    } else {
        match cli.verbose {
            0 => "warn",
            1 => "info",
            2 => "debug",
            _ => "trace",
        }
    };

    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| format!("{{project_name}}={}", filter).into()),
        )
        .with(tracing_subscriber::fmt::layer())
        .init();

    // Create application configuration
    let config = AppConfig {
        verbose: cli.verbose,
        quiet: cli.quiet,
        config_path: cli.config,
    };

    // Create and run application
    let app = App::new(config);
    app.run(cli).await?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    #[tokio::test]
    async fn test_process_files() {
        let config = AppConfig::default();
        let app = App::new(config);

        let temp_dir = tempfile::tempdir().unwrap();
        let input_path = temp_dir.path().join("test.txt");
        std::fs::write(&input_path, "test content").unwrap();

        let result = app.process_files(input_path, None, None, false).await;

        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_generate_report() {
        let config = AppConfig::default();
        let app = App::new(config);

        let result = app.generate_report(OutputFormat::Json, false).await;

        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_validate_config() {
        let config = AppConfig::default();
        let app = App::new(config);

        let temp_dir = tempfile::tempdir().unwrap();
        let config_path = temp_dir.path().join("config.toml");
        std::fs::write(&config_path, "test = true").unwrap();

        let result = app.validate_config(config_path).await;

        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_show_version() {
        let config = AppConfig::default();
        let app = App::new(config);

        let result = app.show_version().await;

        assert!(result.is_ok());
    }
}
