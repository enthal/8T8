use thiserror::Error;

#[derive(Debug, Error)]
#[error("Error on line {line_number}: {message}")]
pub(crate) struct ParseError {
    line_number: usize,
    message: String,
}

impl ParseError {
    pub(crate) fn new(line_number: usize, message: &str) -> Self {
        ParseError {
            line_number,
            message: message.to_string(),
        }
    }
}
