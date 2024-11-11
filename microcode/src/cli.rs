use clap::Parser;

#[derive(Parser)]
#[command(name = "Microcode Compiler")]
#[command(author = "Your Name")]
#[command(version = "1.0")]
#[command(about = "Compiles microcode into ROM images", long_about = None)]
pub(crate) struct Cli {
    /// Input file (defaults to stdin)
    #[arg(short, long)]
    pub(crate) input: Option<String>,

    /// Output file prefix (defaults to stdout)
    #[arg(short, long)]
    pub(crate) output: Option<String>,

    /// Output format: "hex" or "binary"
    #[arg(short, long, default_value = "hex")]
    pub(crate) format: String,
}
