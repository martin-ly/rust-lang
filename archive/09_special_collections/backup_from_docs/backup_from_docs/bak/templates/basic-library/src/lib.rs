//! {{project_description}}
//!
//! This crate provides {{project_description_lower}}.
//!
//! # Examples
//!
//! ```rust
//! use {{project_name}}::*;
//!
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! let result = {{project_name}}::process_data("example")?;
//! println!("Result: {}", result);
//! # Ok(())
//! # }
//! ```
//!
//! # Features
//!
//! - `std` (default): Enable standard library features
//! - `doc`: Enable documentation features

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]
#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![warn(clippy::nursery)]

use anyhow::Result;
use thiserror::Error;

/// Errors that can occur in {{project_name}}
#[derive(Error, Debug)]
pub enum {{ProjectName}}Error {
    /// Invalid input error
    #[error("Invalid input: {message}")]
    InvalidInput { message: String },

    /// Processing error
    #[error("Processing failed: {message}")]
    ProcessingError { message: String },

    /// IO error
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
}

/// Result type for {{project_name}}
pub type {{ProjectName}}Result<T> = Result<T, {{ProjectName}}Error>;

/// Main {{project_name}} struct
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct {{ProjectName}} {
    /// Configuration for {{project_name}}
    pub config: {{ProjectName}}Config,
}

/// Configuration for {{project_name}}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct {{ProjectName}}Config {
    /// Whether to enable verbose output
    pub verbose: bool,

    /// Maximum retry count
    pub max_retries: u32,

    /// Timeout in seconds
    pub timeout_seconds: u64,
}

impl Default for {{ProjectName}}Config {
    fn default() -> Self {
        Self {
            verbose: false,
            max_retries: 3,
            timeout_seconds: 30,
        }
    }
}

impl {{ProjectName}} {
    /// Create a new {{project_name}} instance
    ///
    /// # Examples
    ///
    /// ```rust
    /// use {{project_name}}::{{ProjectName}};
    ///
    /// let {{project_name}} = {{ProjectName}}::new();
    /// ```
    pub fn new() -> Self {
        Self::with_config({{ProjectName}}Config::default())
    }

    /// Create a new {{project_name}} instance with configuration
    ///
    /// # Examples
    ///
    /// ```rust
    /// use {{project_name}}::{ {{ProjectName}}, {{ProjectName}}Config };
    ///
    /// let config = {{ProjectName}}Config {
    ///     verbose: true,
    ///     max_retries: 5,
    ///     timeout_seconds: 60,
    /// };
    /// let {{project_name}} = {{ProjectName}}::with_config(config);
    /// ```
    pub fn with_config(config: {{ProjectName}}Config) -> Self {
        Self { config }
    }

    /// Process data
    ///
    /// # Arguments
    ///
    /// * `input` - The input data to process
    ///
    /// # Returns
    ///
    /// Returns a result containing the processed data or an error
    ///
    /// # Examples
    ///
    /// ```rust
    /// use {{project_name}}::{{ProjectName}};
    ///
    /// # fn main() -> {{project_name}}::{{ProjectName}}Result<()> {
    /// let {{project_name}} = {{ProjectName}}::new();
    /// let result = {{project_name}}.process_data("example")?;
    /// println!("Processed: {}", result);
    /// # Ok(())
    /// # }
    /// ```
    pub fn process_data(&self, input: &str) -> {{ProjectName}}Result<String> {
        if input.is_empty() {
            return Err({{ProjectName}}Error::InvalidInput {
                message: "Input cannot be empty".to_string(),
            });
        }

        if self.config.verbose {
            println!("Processing input: {}", input);
        }

        // Simulate processing
        let result = format!("Processed: {}", input);

        if self.config.verbose {
            println!("Processing complete: {}", result);
        }

        Ok(result)
    }

    /// Process data with retries
    ///
    /// # Arguments
    ///
    /// * `input` - The input data to process
    ///
    /// # Returns
    ///
    /// Returns a result containing the processed data or an error
    ///
    /// # Examples
    ///
    /// ```rust
    /// use {{project_name}}::{{ProjectName}};
    ///
    /// # fn main() -> {{project_name}}::{{ProjectName}}Result<()> {
    /// let {{project_name}} = {{ProjectName}}::new();
    /// let result = {{project_name}}.process_data_with_retries("example")?;
    /// println!("Processed with retries: {}", result);
    /// # Ok(())
    /// # }
    /// ```
    pub fn process_data_with_retries(&self, input: &str) -> {{ProjectName}}Result<String> {
        let mut last_error = None;

        for attempt in 1..=self.config.max_retries {
            if self.config.verbose {
                println!("Attempt {} of {}", attempt, self.config.max_retries);
            }

            match self.process_data(input) {
                Ok(result) => return Ok(result),
                Err(e) => {
                    last_error = Some(e);
                    if attempt < self.config.max_retries {
                        // Wait before retry (simplified)
                        std::thread::sleep(std::time::Duration::from_millis(100));
                    }
                }
            }
        }

        Err(last_error.unwrap_or_else(|| {{ProjectName}}Error::ProcessingError {
            message: "All retry attempts failed".to_string(),
        }))
    }
}

impl Default for {{ProjectName}} {
    fn default() -> Self {
        Self::new()
    }
}

/// Process data using the default configuration
///
/// # Arguments
///
/// * `input` - The input data to process
///
/// # Returns
///
/// Returns a result containing the processed data or an error
///
/// # Examples
///
/// ```rust
/// use {{project_name}}::process_data;
///
/// # fn main() -> {{project_name}}::{{ProjectName}}Result<()> {
/// let result = process_data("example")?;
/// println!("Result: {}", result);
/// # Ok(())
/// # }
/// ```
pub fn process_data(input: &str) -> {{ProjectName}}Result<String> {
    {{ProjectName}}::new().process_data(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let {{project_name}} = {{ProjectName}}::new();
        assert!(!{{project_name}}.config.verbose);
        assert_eq!({{project_name}}.config.max_retries, 3);
        assert_eq!({{project_name}}.config.timeout_seconds, 30);
    }

    #[test]
    fn test_with_config() {
        let config = {{ProjectName}}Config {
            verbose: true,
            max_retries: 5,
            timeout_seconds: 60,
        };
        let {{project_name}} = {{ProjectName}}::with_config(config.clone());
        assert_eq!({{project_name}}.config, config);
    }

    #[test]
    fn test_process_data_success() {
        let {{project_name}} = {{ProjectName}}::new();
        let result = {{project_name}}.process_data("test");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "Processed: test");
    }

    #[test]
    fn test_process_data_empty_input() {
        let {{project_name}} = {{ProjectName}}::new();
        let result = {{project_name}}.process_data("");
        assert!(result.is_err());
        match result.unwrap_err() {
            {{ProjectName}}Error::InvalidInput { message } => {
                assert_eq!(message, "Input cannot be empty");
            }
            _ => panic!("Expected InvalidInput error"),
        }
    }

    #[test]
    fn test_process_data_with_retries_success() {
        let {{project_name}} = {{ProjectName}}::new();
        let result = {{project_name}}.process_data_with_retries("test");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "Processed: test");
    }

    #[test]
    fn test_process_data_function() {
        let result = process_data("test");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "Processed: test");
    }

    #[test]
    fn test_default() {
        let {{project_name}} = {{ProjectName}}::default();
        assert!(!{{project_name}}.config.verbose);
        assert_eq!({{project_name}}.config.max_retries, 3);
        assert_eq!({{project_name}}.config.timeout_seconds, 30);
    }
}
