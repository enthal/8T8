/// Represents a control line (single-bit or multi-bit)
#[derive(Debug, Clone)]
pub(crate) enum ControlLine {
    SingleBit { name: String, active_low: bool },
    MultiBit { name: String, width: usize },
}

/// Represents a microcode word for a specific address
#[derive(Debug, PartialEq)]
pub(crate) struct MicrocodeWord {
    pub(crate) bits: Vec<BitValue>,
}

/// Represents the value of a bit in the microcode word
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum BitValue {
    Default,
    Active,
    Inactive,
}
