mod cli;
mod ds;
mod error;
mod parser;

use std::io::{self, BufRead, BufReader};

use clap::Parser;
use cli::Cli;
use parser::ParserState;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();

    let reader: Box<dyn BufRead> = match &cli.input {
        Some(filename) => Box::new(BufReader::new(std::fs::File::open(filename)?)),
        None => Box::new(BufReader::new(io::stdin())),
    };

    let mut parser = ParserState::new();
    parser.parse(reader)?;
    parser.generate_output(&cli)?;

    Ok(())
}
