use clap::Parser;

#[derive(Parser, Debug, Clone)]
/// IC3
pub struct Options {
    /// input aiger file
    pub model: String,

    /// verbose level
    #[arg(short, default_value_t = 1)]
    pub verbose: usize,
}

impl Default for Options {
    fn default() -> Self {
        Options::parse_from([""])
    }
}
