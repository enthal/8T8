use crate::{
    ds::{BitValue, ControlLine, MicrocodeWord},
    error::ParseError,
};
use std::io::BufRead;
use std::io::Write;
use std::{
    collections::{HashMap, HashSet},
    fs::File,
};

#[derive(Debug)]
pub(crate) struct ParserState {
    line_number: usize,
    control_lines: Vec<ControlLine>,
    control_line_names: HashSet<String>,
    multibit_aliases: HashMap<String, HashMap<String, u32>>,
    current_address: u32,
    microcode_words: HashMap<u32, MicrocodeWord>,
    max_address: u32,
}

impl ParserState {
    pub(crate) fn new() -> Self {
        ParserState {
            line_number: 0,
            control_lines: Vec::new(),
            control_line_names: HashSet::new(),
            multibit_aliases: HashMap::new(),
            current_address: 0,
            microcode_words: HashMap::new(),
            max_address: 0,
        }
    }

    /// Helper method to create a ParseError with the current line number
    fn parse_error(&self, message: &str) -> ParseError {
        ParseError::new(self.line_number, message)
    }
}

impl ParserState {
    pub(crate) fn parse<R: BufRead>(&mut self, reader: R) -> Result<(), ParseError> {
        let mut lines = reader.lines();
        while let Some(line) = lines.next() {
            self.line_number += 1;
            let line =
                line.map_err(|e| self.parse_error(&format!("Failed to read line: {}", e)))?;
            let line = line.split('#').next().unwrap_or_default().trim();
            if line.is_empty() {
                continue; // Skip comments and empty lines
            }
            let (first_char, rest) = line.split_at(1);
            match first_char {
                "@" => self.parse_control_line(rest)?,
                "~" => self.parse_alias_line(rest)?,
                ">" => self.parse_address_line(rest)?,
                "=" => self.parse_microcode_line(rest)?,
                _ => {
                    return Err(self.parse_error(&format!("Invalid line start '{}'", first_char)));
                }
            }
        }
        Ok(())
    }
}

impl ParserState {
    fn parse_control_line(&mut self, line: &str) -> Result<(), ParseError> {
        let terms = line.split_whitespace();
        for term in terms {
            let mut active_low = false;
            let mut name = term;
            if term.starts_with('/') {
                active_low = true;
                name = &term[1..];
            }

            if name.contains('/') {
                // Multi-bit term
                let parts: Vec<&str> = name.split('/').collect();
                if parts.len() != 2 {
                    return Err(self.parse_error(&format!(
                        "Invalid multibit term '{}', expected format 'name/width'",
                        name
                    )));
                }
                let name = parts[0];
                let width_str = parts[1];
                let width: usize = width_str.parse().map_err(|_| {
                    self.parse_error(&format!(
                        "Invalid width '{}' in multibit term '{}'",
                        width_str, name
                    ))
                })?;
                if width == 0 {
                    return Err(self.parse_error(&format!(
                        "Width cannot be zero in multibit term '{}'",
                        name
                    )));
                }
                if self.control_line_names.contains(name) {
                    return Err(self
                        .parse_error(&format!("Control line '{}' defined more than once", name)));
                }
                self.control_lines.push(ControlLine::MultiBit {
                    name: name.to_string(),
                    width,
                });
                self.control_line_names.insert(name.to_string());
            } else {
                // Single-bit term
                if name.is_empty() || !name.chars().all(char::is_alphanumeric) {
                    return Err(self.parse_error(&format!(
                        "Invalid control line name '{}', must be alphanumeric",
                        name
                    )));
                }
                if name.chars().all(char::is_numeric) {
                    return Err(self.parse_error(&format!(
                        "Control line name '{}' cannot be all numerals",
                        name
                    )));
                }
                if self.control_line_names.contains(name) {
                    return Err(self
                        .parse_error(&format!("Control line '{}' defined more than once", name)));
                }
                self.control_lines.push(ControlLine::SingleBit {
                    name: name.to_string(),
                    active_low,
                });
                self.control_line_names.insert(name.to_string());
            }
        }
        Ok(())
    }
}

impl ParserState {
    fn parse_alias_line(&mut self, line: &str) -> Result<(), ParseError> {
        let mut tokens = line.split_whitespace();
        let multibit_name = tokens
            .next()
            .ok_or_else(|| self.parse_error("Missing multibit term name after '~'"))?;

        let control_line = self
            .control_lines
            .iter()
            .find(|cl| match cl {
                ControlLine::SingleBit { name, .. } => name == multibit_name,
                ControlLine::MultiBit { name, .. } => name == multibit_name,
            })
            .ok_or_else(|| {
                self.parse_error(&format!(
                    "Undefined term '{}' in alias definition",
                    multibit_name
                ))
            })?;

        let width = if let ControlLine::MultiBit { width, .. } = control_line {
            *width
        } else {
            return Err(self.parse_error(&format!(
                "Control line '{}' is not a multibit term and cannot have aliases",
                multibit_name
            )));
        };

        let expected_aliases = 1 << width;
        let mut aliases = HashMap::new();
        for (i, alias) in tokens.enumerate() {
            if i >= expected_aliases {
                return Err(self.parse_error(&format!(
                    "Too many aliases for multibit term '{}', expected {} aliases",
                    multibit_name, expected_aliases
                )));
            }
            if alias.chars().all(char::is_numeric) {
                return Err(
                    self.parse_error(&format!("Alias name '{}' cannot be all numerals", alias))
                );
            }
            if aliases.contains_key(alias) {
                return Err(self.parse_error(&format!(
                    "Alias '{}' defined more than once for multibit term '{}'",
                    alias, multibit_name
                )));
            }
            aliases.insert(alias.to_string(), i as u32);
        }
        if aliases.len() < expected_aliases {
            return Err(self.parse_error(&format!(
                "Not enough aliases for multibit term '{}', expected {} aliases",
                multibit_name, expected_aliases
            )));
        }
        self.multibit_aliases
            .insert(multibit_name.to_string(), aliases);
        Ok(())
    }
}

impl ParserState {
    fn parse_address_line(&mut self, line: &str) -> Result<(), ParseError> {
        let line = line.trim();
        if line.is_empty() {
            return Err(self.parse_error("Missing address after '>'"));
        }

        let (radix, addr_str) = match line.chars().next() {
            Some('h') => (16, &line[1..]),
            Some('d') => (10, &line[1..]),
            Some('b') => (2, &line[1..]),
            _ => (10, line),
        };

        self.current_address = u32::from_str_radix(addr_str, radix)
            .map_err(|_| self.parse_error(&format!("Invalid address format '{}'", addr_str)))?;

        Ok(())
    }
}

impl ParserState {
    fn parse_microcode_line(&mut self, line: &str) -> Result<(), ParseError> {
        if self.microcode_words.contains_key(&self.current_address) {
            return Err(self.parse_error(&format!(
                "Microcode already defined for address {}",
                self.current_address
            )));
        }

        let terms = line.split_whitespace();
        let mut bit_values = vec![BitValue::Default; self.total_bit_width()];
        for term in terms {
            if term.contains('=') {
                // Assignment to multibit term
                let parts: Vec<&str> = term.split('=').collect();
                if parts.len() != 2 {
                    return Err(self.parse_error(&format!(
                        "Invalid assignment '{}', expected format 'name=value'",
                        term
                    )));
                }
                let name = parts[0];
                let value_str = parts[1];

                // Find the control line
                let control_line = self
                    .control_lines
                    .iter()
                    .find(|cl| match cl {
                        ControlLine::MultiBit { name: cl_name, .. } => cl_name == name,
                        _ => false,
                    })
                    .ok_or_else(|| {
                        self.parse_error(&format!(
                            "Undefined multibit control line '{}' in assignment '{}'",
                            name, term
                        ))
                    })?;
                let width = if let ControlLine::MultiBit { width, .. } = control_line {
                    *width
                } else {
                    unreachable!()
                };

                // Resolve the value
                let value = if let Some(aliases) = self.multibit_aliases.get(name) {
                    if let Some(&val) = aliases.get(value_str) {
                        val
                    } else {
                        value_str.parse::<u32>().map_err(|_| {
                            self.parse_error(&format!(
                                "Invalid value '{}' for multibit term '{}'",
                                value_str, name
                            ))
                        })?
                    }
                } else {
                    value_str.parse::<u32>().map_err(|_| {
                        self.parse_error(&format!(
                            "Invalid value '{}' for multibit term '{}'",
                            value_str, name
                        ))
                    })?
                };

                if value >= (1 << width) {
                    return Err(self.parse_error(&format!(
                        "Value '{}' exceeds width {} of multibit term '{}'",
                        value, width, name
                    )));
                }

                // Set the bits in bit_values
                let bit_positions = self.get_bit_positions(name)?;
                for (i, &bit_pos) in bit_positions.iter().enumerate() {
                    let bit = (value >> (width - 1 - i)) & 1;
                    bit_values[bit_pos] = if bit == 1 {
                        BitValue::Active
                    } else {
                        BitValue::Inactive
                    };
                }
            } else {
                // Single-bit term
                if !self.control_line_names.contains(term) {
                    return Err(self.parse_error(&format!("Undefined control line '{}'", term)));
                }
                let bit_pos = self.get_bit_position(term)?;
                bit_values[bit_pos] = BitValue::Active;
            }
        }

        self.microcode_words
            .insert(self.current_address, MicrocodeWord { bits: bit_values });
        if self.current_address > self.max_address {
            self.max_address = self.current_address;
        }
        self.current_address += 1;
        Ok(())
    }
}

impl ParserState {
    fn total_bit_width(&self) -> usize {
        self.control_lines
            .iter()
            .map(|cl| match cl {
                ControlLine::SingleBit { .. } => 1,
                ControlLine::MultiBit { width, .. } => *width,
            })
            .sum()
    }

    fn get_bit_positions(&self, name: &str) -> Result<Vec<usize>, ParseError> {
        let mut positions = Vec::new();
        let mut current_pos = 0;
        for cl in &self.control_lines {
            match cl {
                ControlLine::SingleBit { name: cl_name, .. } => {
                    if cl_name == name {
                        positions.push(current_pos);
                        return Ok(positions);
                    }
                    current_pos += 1;
                }
                ControlLine::MultiBit {
                    name: cl_name,
                    width,
                } => {
                    if cl_name == name {
                        positions.extend(current_pos..current_pos + width);
                        return Ok(positions);
                    }
                    current_pos += width;
                }
            }
        }
        Err(self.parse_error(&format!("Control line '{}' not found", name)))
    }

    fn get_bit_position(&self, name: &str) -> Result<usize, ParseError> {
        let positions = self.get_bit_positions(name)?;
        positions
            .get(0)
            .cloned()
            .ok_or_else(|| self.parse_error(&format!("Control line '{}' not found", name)))
    }
}

impl ParserState {
    pub(crate) fn generate_output(&self, cli: &crate::cli::Cli) -> Result<(), ParseError> {
        let total_bits = self.total_bit_width();
        let partitions = ((total_bits + 7) / 8) as usize;

        let address_space = (self.max_address + 1).next_power_of_two();

        // Prepare default values
        let default_bits: Vec<BitValue> = self
            .control_lines
            .iter()
            .flat_map(|cl| match cl {
                ControlLine::SingleBit { active_low, .. } => {
                    vec![if *active_low {
                        BitValue::Active
                    } else {
                        BitValue::Inactive
                    }]
                }
                ControlLine::MultiBit { width, .. } => vec![BitValue::Inactive; *width],
            })
            .collect();

        // Initialize ROM partitions
        let mut roms: Vec<Vec<u8>> = vec![vec![0; address_space as usize]; partitions];

        for address in 0..address_space {
            let microcode_word = self.microcode_words.get(&address);
            let bit_values = if let Some(word) = microcode_word {
                word.bits.clone()
            } else {
                // Use default bits
                default_bits.clone()
            };

            // Convert bit_values to bytes per partition
            for p in 0..partitions {
                let mut byte = 0u8;
                for i in 0..8 {
                    let bit_index = p * 8 + i;
                    let bit = if bit_index < bit_values.len() {
                        match bit_values[bit_index] {
                            BitValue::Active => 1,
                            BitValue::Inactive => 0,
                            BitValue::Default => {
                                // Should not occur here
                                0
                            }
                        }
                    } else {
                        // Pad with zeros if there are fewer bits
                        0
                    };
                    byte |= bit << (7 - i); // Bits are from MSB to LSB
                }
                roms[p][address as usize] = byte;
            }
        }

        // Write output files
        for (i, rom_data) in roms.iter().enumerate() {
            let filename = if let Some(prefix) = &cli.output {
                format!("{}_{}.{}", prefix, i, cli.format)
            } else {
                format!("rom_{}.{}", i, cli.format)
            };
            let mut file = File::create(&filename).map_err(|e| {
                self.parse_error(&format!("File error creating '{}': {}", filename, e))
            })?;

            match cli.format.as_str() {
                "hex" => {
                    for byte in rom_data {
                        writeln!(file, "{:02X}", byte).map_err(|e| {
                            self.parse_error(&format!("Write error to file '{}': {}", filename, e))
                        })?;
                    }
                }
                "binary" => {
                    use std::io::Write;
                    file.write_all(rom_data).map_err(|e| {
                        self.parse_error(&format!("Write error to file '{}': {}", filename, e))
                    })?;
                }
                _ => {
                    return Err(
                        self.parse_error(&format!("Unknown output format '{}'", cli.format))
                    );
                }
            }
        }

        Ok(())
    }
}

// Place the expanded test suite here, as detailed in previous responses.
#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    /// Helper function to create a ParserState and parse the given input
    fn parse_input(input: &str) -> Result<ParserState, ParseError> {
        let mut parser = ParserState::new();
        let reader = Cursor::new(input);
        parser.parse(reader)?;
        Ok(parser)
    }

    #[test]
    fn test_valid_input_all_line_types() {
        // This test includes all four line types (@, ~, >, =)
        let input = r#"
            # Define control lines
            @ /x0 x1 x2 x3 x4 a b /c zz/4

            # Define aliases for multibit term zz
            ~ zz zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen

            # Set starting address
            > d0

            # Define microcode words
            = a zz=three
            = b zz=fifteen
            = c zz=zero
        "#;

        let parser = parse_input(input).expect("Parsing failed");
        assert_eq!(parser.control_lines.len(), 9);
        assert_eq!(parser.multibit_aliases.len(), 1);
        assert_eq!(parser.microcode_words.len(), 3);
        assert_eq!(parser.max_address, 2);

        // Verify that the aliases were correctly parsed
        let zz_aliases = parser.multibit_aliases.get("zz").unwrap();
        assert_eq!(zz_aliases.get("three"), Some(&3));
        assert_eq!(zz_aliases.get("fifteen"), Some(&15));
    }

    #[test]
    fn test_error_duplicate_control_line() {
        let input = "@ a\n@ a";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 2: Control line 'a' defined more than once"
        );
    }

    #[test]
    fn test_error_invalid_multibit_width() {
        let input = "@ xx/0";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 1: Width cannot be zero in multibit term 'xx'"
        );
    }

    #[test]
    fn test_error_alias_name_all_numerals() {
        let input = "@ ww/2\n~ ww 12 3 4 5";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 2: Alias name '12' cannot be all numerals"
        );
    }

    #[test]
    fn test_error_too_many_aliases() {
        let input = "@ ww/2\n~ ww a b c d e";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 2: Too many aliases for multibit term 'ww', expected 4 aliases"
        );
    }

    #[test]
    fn test_error_too_few_aliases() {
        let input = "@ ww/2\n~ ww a b";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 2: Not enough aliases for multibit term 'ww', expected 4 aliases"
        );
    }

    #[test]
    fn test_error_invalid_address_format() {
        let input = ">\n=";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 1: Missing address after '>'"
        );
    }

    #[test]
    fn test_error_undefined_control_line_in_microcode() {
        let input = "@ a\n= b";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 2: Undefined control line 'b'"
        );
    }

    #[test]
    fn test_error_value_exceeds_multibit_width() {
        let input = "@ zz/2\n= zz=5";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 2: Value '5' exceeds width 2 of multibit term 'zz'"
        );
    }

    #[test]
    fn test_error_microcode_defined_more_than_once() {
        let input = "@ a\n= a\n> 0\n= a";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 4: Microcode already defined for address 0"
        );
    }

    #[test]
    fn test_error_invalid_assignment_format() {
        let input = "@ zz/2\n= zz==3";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 2: Invalid assignment 'zz==3', expected format 'name=value'"
        );
    }

    #[test]
    fn test_error_undefined_multibit_term_in_assignment() {
        let input = "@ a\n= zz=3";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 2: Undefined multibit control line 'zz' in assignment 'zz=3'"
        );
    }

    #[test]
    fn test_valid_input_with_comments_and_blank_lines() {
        let input = r#"
            # Define control lines with comments and blank lines

            @ /reset load increment /enable data/4

            ~ data  zero one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen

            > h0

            = load data=fifteen   # Set data to fifteen
            =
            # Next microcode word
            = increment data=one
        "#;

        let parser = parse_input(input).expect("Parsing failed");
        assert_eq!(parser.control_lines.len(), 5);
        assert_eq!(parser.microcode_words.len(), 3);
    }

    #[test]
    fn test_valid_input_single_bit_active_low() {
        let input = r#"
            @ /enable
            = enable
        "#;

        let parser = parse_input(input).expect("Parsing failed");
        let microcode_word = parser.microcode_words.get(&0).unwrap();

        // Since 'enable' is active low and activated in the microcode,
        // the bit should be inactive (since active low is 1 when inactive)
        let bit_value = microcode_word.bits[0];
        match bit_value {
            BitValue::Active => {}
            _ => panic!("Expected BitValue::Active for 'enable'"),
        }
    }

    #[test]
    fn test_valid_input_multibit_value_as_number() {
        let input = r#"
            @ data/4
            = data=10
        "#;

        let parser = parse_input(input).expect("Parsing failed");
        let microcode_word = parser.microcode_words.get(&0).unwrap();

        // The bits for 'data' should represent the binary value 1010
        let bit_positions = parser.get_bit_positions("data").unwrap();
        let expected_bits = vec![1, 0, 1, 0]; // From MSB to LSB

        for (i, &bit_pos) in bit_positions.iter().enumerate() {
            let bit_value = microcode_word.bits[bit_pos];
            let expected_bit = expected_bits[i];
            match bit_value {
                BitValue::Active if expected_bit == 1 => {}
                BitValue::Inactive if expected_bit == 0 => {}
                _ => panic!(
                    "Bit at position {} expected to be {}, found {:?}",
                    bit_pos, expected_bit, bit_value
                ),
            }
        }
    }

    #[test]
    fn test_valid_input_address_increment() {
        let input = r#"
            @ a b c
            > d0
            = a
            = b
            = c
        "#;

        let parser = parse_input(input).expect("Parsing failed");
        assert_eq!(parser.microcode_words.len(), 3);
        assert_eq!(parser.microcode_words.contains_key(&0), true);
        assert_eq!(parser.microcode_words.contains_key(&1), true);
        assert_eq!(parser.microcode_words.contains_key(&2), true);
    }

    #[test]
    fn test_valid_input_with_hex_and_binary_addresses() {
        let input = r#"
            @ x y z
            > hA
            = x
            > b1011
            = y
        "#;

        let parser = parse_input(input).expect("Parsing failed");
        assert_eq!(parser.microcode_words.len(), 2);
        assert_eq!(parser.microcode_words.contains_key(&10), true); // hA is 10
        assert_eq!(parser.microcode_words.contains_key(&11), true); // b1010 is 11
        assert_eq!(
            parser.microcode_words,
            HashMap::from([
                (
                    10,
                    MicrocodeWord {
                        bits: [BitValue::Active, BitValue::Default, BitValue::Default].to_vec()
                    }
                ),
                (
                    11,
                    MicrocodeWord {
                        bits: [BitValue::Default, BitValue::Active, BitValue::Default].to_vec()
                    }
                ),
            ])
        );
    }

    #[test]
    fn test_error_control_line_name_all_numerals() {
        let input = "@ 123";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 1: Control line name '123' cannot be all numerals"
        );
    }

    #[test]
    fn test_error_invalid_line_start() {
        let input = "& invalid line start";
        let err = parse_input(input).unwrap_err();
        assert_eq!(err.to_string(), "Error on line 1: Invalid line start '&'");
    }

    #[test]
    fn test_error_missing_multibit_term_after_tilde() {
        let input = "~";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 1: Missing multibit term name after '~'"
        );
    }

    #[test]
    fn test_error_multibit_alias_for_single_bit_term() {
        let input = "@ a\n~ a alias";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 2: Control line 'a' is not a multibit term and cannot have aliases"
        );
    }

    #[test]
    fn test_error_undefined_multibit_term_in_alias() {
        let input = "~ zz alias1 alias2";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 1: Undefined term 'zz' in alias definition"
        );
    }

    #[test]
    fn test_error_invalid_value_in_assignment() {
        let input = "@ zz/2\n= zz=invalid";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 2: Invalid value 'invalid' for multibit term 'zz'"
        );
    }

    #[test]
    fn test_error_missing_address_after_greater_than() {
        let input = ">";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 1: Missing address after '>'"
        );
    }

    #[test]
    fn test_error_invalid_address_prefix() {
        let input = "> x123";
        let err = parse_input(input).unwrap_err();
        assert_eq!(
            err.to_string(),
            "Error on line 1: Invalid address format 'x123'"
        );
    }
}
