use std::collections::HashMap;
use std::fmt::Display;

use byteorder::{BigEndian, LittleEndian, WriteBytesExt};
use pest::iterators::{Pair, Pairs};
use pest::Parser;
use pest_derive::Parser;
use thiserror::Error;

#[derive(Parser)]
#[grammar = "chipasm.pest"]
struct ChipAssemblyParser;

pub struct ChipAssembler;

#[derive(Debug, Error)]
pub enum AssemblyError {
    Parse(anyhow::Error),
    Token(String, (usize, usize)),
    Compile(String, (usize, usize)),
}

impl Display for AssemblyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

fn read_next<'pair>(
    from: &mut Pairs<'pair, Rule>,
    at: (usize, usize),
    expected: &'static [Rule],
    allow_more: bool,
) -> Result<Vec<Pair<'pair, Rule>>, AssemblyError> {
    let mut rules = Vec::new();
    for expected_rule in expected {
        let next = from
            .find(|p| p.as_rule() != Rule::whitespace)
            .ok_or(AssemblyError::Token("Expected parameter".to_string(), at))?;
        if next.as_rule() != *expected_rule {
            return Err(AssemblyError::Token(
                format!("Expected '{:?}', got {:?}", expected_rule, next.as_rule()),
                at,
            ));
        }
        rules.push(next);
    }

    // make sure there's no extra parameters
    if !allow_more && let Some(next) = from.find(|r| r.as_rule() != Rule::whitespace) {
        Err(AssemblyError::Token(
            format!("Unexpected parameter '{}'", next.as_str()),
            next.line_col(),
        ))?;
    }

    Ok(rules)
}

fn expect<'pair>(
    pair: Pair<'pair, Rule>,
    expected: &'static [Rule],
) -> Result<Pair<'pair, Rule>, AssemblyError> {
    if expected.iter().any(|e| *e == pair.as_rule()) {
        Ok(pair)
    } else {
        Err(AssemblyError::Token(
            format!(
                "Unexpected token '{}', expected {:?}",
                pair.as_str(),
                expected
            ),
            pair.line_col(),
        ))
    }
}

fn expect_number(pair: Pair<'_, Rule>) -> Result<u16, AssemblyError> {
    let number = expect(pair, &[Rule::parameter_hex, Rule::parameter_num])?;
    match number.as_rule() {
        Rule::parameter_hex => {
            let val_str = number.as_str().trim_start_matches("0x");
            let val = i32::from_str_radix(val_str, 16).map_err(|e| {
                AssemblyError::Token(
                    format!("Invalid number value '{}'", val_str),
                    number.line_col(),
                )
            })?;
            Ok(val as u16)
        }
        Rule::parameter_num => {
            let val = number.as_str().parse::<i32>().map_err(|_| {
                AssemblyError::Token(
                    format!("Invalid number value '{}'", number.as_str()),
                    number.line_col(),
                )
            })?;
            Ok(val as u16)
        }
        _ => Err(AssemblyError::Token(
            format!("Expected number, found '{}'", number.as_str()),
            number.line_col(),
        ))?,
    }
}

fn expect_v_register(pair: Pair<'_, Rule>) -> Result<u8, AssemblyError> {
    let register = expect(pair, &[Rule::parameter_register])?;
    let register_num = str::parse::<u8>(register.as_str().to_lowercase().trim_start_matches("v"))
        .map_err(|_| {
        AssemblyError::Token(
            format!("Invalid register value '{}'", register.as_str()),
            register.line_col(),
        )
    })?;

    if register_num > 0xf {
        return Err(AssemblyError::Token(
            format!("Invalid register '{}'", register.as_str()),
            register.line_col(),
        ));
    }

    Ok(register_num)
}

fn write_instruction_regxnn<F: Fn(u16, u16) -> u16>(
    segment: &mut Vec<u8>,
    pairs: &mut Pairs<'_, Rule>,
    at: (usize, usize),
    to_inst: F,
) -> Result<(), AssemblyError> {
    let mut parameters =
        read_next(pairs, at, &[Rule::parameter, Rule::parameter], false)?.into_iter();
    let register =
        expect_v_register(parameters.next().unwrap().into_inner().next().unwrap())? as u16;
    let val = expect_number(parameters.next().unwrap().into_inner().next().unwrap())?;
    let instruction = to_inst(register, val);
    segment.write_u16::<BigEndian>(instruction).unwrap();
    Ok(())
}

fn write_instruction_regxnn_or_xy<Fa: Fn(u16, u16) -> u16, Fb: Fn(u16, u16) -> u16>(
    segment: &mut Vec<u8>,
    pairs: &mut Pairs<'_, Rule>,
    at: (usize, usize),
    to_inst_xnn: Fa,
    to_inst_xy: Fb,
) -> Result<(), AssemblyError> {
    let mut parameters =
        read_next(pairs, at, &[Rule::parameter, Rule::parameter], false)?.into_iter();
    let register =
        expect_v_register(parameters.next().unwrap().into_inner().next().unwrap())? as u16;
    let next = parameters.next().unwrap().into_inner().next().unwrap();
    let instruction = if next.as_rule() == Rule::parameter_register {
        let val = expect_v_register(next)? as u16;
        to_inst_xy(register, val)
    } else {
        let val = expect_number(next)?;
        to_inst_xnn(register, val)
    };
    segment.write_u16::<BigEndian>(instruction).unwrap();
    Ok(())
}

fn write_instruction_regxy<F: Fn(u16, u16) -> u16>(
    segment: &mut Vec<u8>,
    pairs: &mut Pairs<'_, Rule>,
    at: (usize, usize),
    to_inst: F,
) -> Result<(), AssemblyError> {
    let mut parameters =
        read_next(pairs, at, &[Rule::parameter, Rule::parameter], false)?.into_iter();
    let register_x =
        expect_v_register(parameters.next().unwrap().into_inner().next().unwrap())? as u16;
    let register_y =
        expect_v_register(parameters.next().unwrap().into_inner().next().unwrap())? as u16;
    let instruction = to_inst(register_x, register_y);
    segment.write_u16::<BigEndian>(instruction).unwrap();
    Ok(())
}

impl ChipAssembler {
    pub fn assemble(input: &str) -> Result<Vec<u8>, AssemblyError> {
        let mut asm = ChipAssemblyParser::parse(Rule::program, input)
            .map_err(|p| AssemblyError::Parse(p.into()))?;
        let program = asm.next();
        if program.is_none() {
            return Ok(Vec::new());
        }
        let program = program.unwrap();

        let mut segments: Vec<(u16, (usize, usize), Vec<u8>)> = Vec::new();
        let mut segment: Vec<u8> = Vec::new();
        let mut labels: HashMap<&str, u16> = HashMap::new();
        let mut unfinished_label_jumps: Vec<(String, (usize, usize), u16)> = Vec::new();
        let mut segment_line_col = (0_usize, 0_usize);
        let mut segment_start = 0_u16;
        for pair in program.into_inner() {
            match pair.as_rule() {
                Rule::whitespace | Rule::whitespace_or_nl => continue,
                Rule::directive => {
                    let line_col = pair.line_col();
                    let mut inner_rules = pair.into_inner();

                    let name = inner_rules
                        .next()
                        .ok_or(AssemblyError::Token(
                            "Expected directive name".to_string(),
                            line_col,
                        ))?
                        .as_str()
                        .to_lowercase();
                    // directive starts a new segment, push last segment if we have one
                    if (name == "location" || name == "entrypoint") && !segment.is_empty() {
                        segments.push((segment_start, segment_line_col, segment));
                        segment = Vec::new();
                        segment_line_col = line_col;
                    }

                    // handle directive
                    match name.as_str() {
                        "location" => {
                            let location =
                                read_next(&mut inner_rules, line_col, &[Rule::parameter], false)?
                                    .into_iter()
                                    .next()
                                    .unwrap();
                            segment_start = expect_number(location.into_inner().next().unwrap())?;
                        }
                        "entrypoint" => {
                            segment_start = 0x200;
                        }
                        _ => {
                            Err(AssemblyError::Token(
                                format!("Unknown directive '{}'", name),
                                line_col,
                            ))?;
                        }
                    };
                }
                Rule::label => {
                    let line_col = pair.line_col();
                    let label_name = pair.into_inner().next().unwrap().as_str();
                    if labels.contains_key(label_name) {
                        Err(AssemblyError::Compile(
                            format!("Redefinition of existing label '{}'", label_name),
                            line_col,
                        ))?;
                    }

                    labels.insert(label_name, segment_start + segment.len() as u16);
                }
                Rule::instruction => {
                    let mut inner_pairs = pair.into_inner();
                    let instruction_name = inner_pairs.next().unwrap();
                    let line_col = instruction_name.line_col();
                    let instruction_name = instruction_name.as_str().to_lowercase();
                    match instruction_name.as_str() {
                        "nop" => {
                            segment.write_u16::<BigEndian>(0x0000).unwrap();
                        }
                        "ret" => {
                            segment.write_u16::<BigEndian>(0x00EE).unwrap();
                        }
                        "halt" => {
                            segment.write_u16::<BigEndian>(0x00FD).unwrap();
                        }
                        "jmp" => {
                            let parameter =
                                read_next(&mut inner_pairs, line_col, &[Rule::parameter], true)?
                                    .into_iter()
                                    .next()
                                    .unwrap();
                            let inner = parameter.into_inner().next().unwrap();
                            let instruction = if inner.as_rule() == Rule::parameter_register {
                                if inner.as_str().to_lowercase() != "v0" {
                                    Err(AssemblyError::Token(
                                        "Only V0 is allowed at this position in this instruction"
                                            .to_string(),
                                        line_col,
                                    ))?;
                                }

                                let parameter = read_next(
                                    &mut inner_pairs,
                                    inner.line_col(),
                                    &[Rule::parameter],
                                    false,
                                )?
                                .into_iter()
                                .next()
                                .unwrap();

                                let address =
                                    expect_number(parameter.into_inner().next().unwrap())?;
                                (address & 0x0fff) | (0xb << 12)
                            } else if inner.as_rule() == Rule::label_name {
                                let line_col = inner.line_col();
                                let label_name = inner.as_str();
                                unfinished_label_jumps.push((
                                    label_name.to_string(),
                                    line_col,
                                    segment_start + segment.len() as u16,
                                ));
                                0_u16
                            } else {
                                let address = expect_number(inner)?;
                                (address & 0x0fff) | (0x1 << 12)
                            };
                            segment.write_u16::<BigEndian>(instruction).unwrap()
                        }
                        "call" => {
                            let parameter =
                                read_next(&mut inner_pairs, line_col, &[Rule::parameter], false)?
                                    .into_iter()
                                    .next()
                                    .unwrap();
                            let address = expect_number(parameter.into_inner().next().unwrap())?;
                            let instruction = (address & 0x0fff) | (0x2 << 12);
                            segment.write_u16::<BigEndian>(instruction).unwrap()
                        }
                        "seq" => write_instruction_regxnn_or_xy(
                            &mut segment,
                            &mut inner_pairs,
                            line_col,
                            |x, nn| (nn & 0xff) | ((x & 0xf) << 8) | (0x3 << 12),
                            |x, y| ((y & 0xf) << 4) | ((x & 0xf) << 8) | (0x5 << 12),
                        )?,
                        "sneq" => write_instruction_regxnn_or_xy(
                            &mut segment,
                            &mut inner_pairs,
                            line_col,
                            |x, nn| (nn & 0xff) | ((x & 0xf) << 8) | (0x4 << 12),
                            |x, y| ((y & 0xf) << 4) | ((x & 0xf) << 8) | (0x9 << 12),
                        )?,
                        "mov" => {
                            let mut parameters = read_next(
                                &mut inner_pairs,
                                line_col,
                                &[Rule::parameter, Rule::parameter],
                                false,
                            )?
                            .into_iter();
                            let first_inner =
                                parameters.next().unwrap().into_inner().next().unwrap();

                            let instruction = if first_inner.as_rule() == Rule::parameter_register
                                && first_inner.as_str().to_lowercase() == "i"
                            {
                                let addr = expect_number(
                                    parameters.next().unwrap().into_inner().next().unwrap(),
                                )?;
                                (addr & 0xfff) | 0xa << 12
                            } else {
                                let register = expect_v_register(first_inner)? as u16;
                                let next = parameters.next().unwrap().into_inner().next().unwrap();
                                if next.as_rule() == Rule::parameter_register {
                                    let val = expect_v_register(next)? as u16;
                                    ((val & 0xf) << 4) | ((register & 0xf) << 8) | (0x8 << 12)
                                } else {
                                    let val = expect_number(next)?;
                                    (val & 0xff) | ((register & 0xf) << 8) | (0x6 << 12)
                                }
                            };
                            segment.write_u16::<BigEndian>(instruction).unwrap()
                        }
                        "add" => {
                            let mut parameters = read_next(
                                &mut inner_pairs,
                                line_col,
                                &[Rule::parameter, Rule::parameter],
                                false,
                            )?
                            .into_iter();
                            let first_inner =
                                parameters.next().unwrap().into_inner().next().unwrap();
                            let instruction = if first_inner.as_rule() == Rule::parameter_register
                                && first_inner.as_str().to_lowercase() == "i"
                            {
                                let register = expect_v_register(
                                    parameters.next().unwrap().into_inner().next().unwrap(),
                                )? as u16;
                                ((register & 0xf) << 8) | 0xf << 12 | 0x1e
                            } else {
                                let register = expect_v_register(first_inner)? as u16;
                                let next = parameters.next().unwrap().into_inner().next().unwrap();
                                if next.as_rule() == Rule::parameter_register {
                                    let val = expect_v_register(next)? as u16;
                                    ((val & 0xf) << 4)
                                        | ((register & 0xf) << 8)
                                        | (0x8 << 12)
                                        | 0x04
                                } else {
                                    let val = expect_number(next)?;
                                    (val & 0xff) | ((register & 0xf) << 8) | (0x7 << 12)
                                }
                            };
                            segment.write_u16::<BigEndian>(instruction).unwrap()
                        }
                        "or" => write_instruction_regxy(
                            &mut segment,
                            &mut inner_pairs,
                            line_col,
                            |x, y| ((x & 0xf) << 8) | ((y & 0xf) << 4) | (0x8 << 12) | 0x1,
                        )?,
                        "and" => write_instruction_regxy(
                            &mut segment,
                            &mut inner_pairs,
                            line_col,
                            |x, y| ((x & 0xf) << 8) | ((y & 0xf) << 4) | (0x8 << 12) | 0x2,
                        )?,
                        "xor" => write_instruction_regxy(
                            &mut segment,
                            &mut inner_pairs,
                            line_col,
                            |x, y| ((x & 0xf) << 8) | ((y & 0xf) << 4) | (0x8 << 12) | 0x3,
                        )?,
                        "sub" => write_instruction_regxy(
                            &mut segment,
                            &mut inner_pairs,
                            line_col,
                            |x, y| ((x & 0xf) << 8) | ((y & 0xf) << 4) | (0x8 << 12) | 0x5,
                        )?,
                        "shr" => write_instruction_regxy(
                            &mut segment,
                            &mut inner_pairs,
                            line_col,
                            |x, y| ((x & 0xf) << 8) | ((y & 0xf) << 4) | (0x8 << 12) | 0x6,
                        )?,
                        "subn" => write_instruction_regxy(
                            &mut segment,
                            &mut inner_pairs,
                            line_col,
                            |x, y| ((x & 0xf) << 8) | ((y & 0xf) << 4) | (0x8 << 12) | 0x7,
                        )?,
                        "shl" => write_instruction_regxy(
                            &mut segment,
                            &mut inner_pairs,
                            line_col,
                            |x, y| ((x & 0xf) << 8) | ((y & 0xf) << 4) | (0x8 << 12) | 0xe,
                        )?,
                        "rand" => write_instruction_regxnn(
                            &mut segment,
                            &mut inner_pairs,
                            line_col,
                            |x, nn| ((x & 0xf) << 8) | (nn & 0xff) | (0xc << 12),
                        )?,
                        "bcd" => {
                            let parameter =
                                read_next(&mut inner_pairs, line_col, &[Rule::parameter], false)?
                                    .into_iter()
                                    .next()
                                    .unwrap();
                            let inner = parameter.into_inner().next().unwrap();
                            let register = expect_v_register(inner)? as u16;
                            segment
                                .write_u16::<BigEndian>(((register & 0xf) << 8) | 0xf << 12 | 0x33)
                                .unwrap()
                        }
                        "save" => {
                            let parameter =
                                read_next(&mut inner_pairs, line_col, &[Rule::parameter], true)?
                                    .into_iter()
                                    .next()
                                    .unwrap();
                            let x =
                                expect_v_register(parameter.into_inner().next().unwrap())? as u16;
                            let next_parameter =
                                inner_pairs.find(|p| p.as_rule() != Rule::whitespace);
                            let instruction = if let Some(next) = next_parameter
                                && next.as_rule() == Rule::parameter
                            {
                                // xo-chip save instruction
                                let y =
                                    expect_v_register(next.into_inner().next().unwrap())? as u16;
                                (0x5 << 12) | ((x & 0xf) << 8) | ((y & 0xf) << 4) | 0x2
                            } else {
                                // regular save instruction
                                (0xf << 12) | ((x & 0xf) << 8) | 0x55
                            };
                            segment.write_u16::<BigEndian>(instruction).unwrap()
                        }
                        "load" => {
                            let parameter =
                                read_next(&mut inner_pairs, line_col, &[Rule::parameter], true)?
                                    .into_iter()
                                    .next()
                                    .unwrap();
                            let x =
                                expect_v_register(parameter.into_inner().next().unwrap())? as u16;
                            let next_parameter =
                                inner_pairs.find(|p| p.as_rule() != Rule::whitespace);
                            let instruction = if let Some(next) = next_parameter
                                && next.as_rule() == Rule::parameter
                            {
                                // xo-chip load instruction
                                let y =
                                    expect_v_register(next.into_inner().next().unwrap())? as u16;
                                (0x5 << 12) | ((x & 0xf) << 8) | ((y & 0xf) << 4) | 0x3
                            } else {
                                // regular load instruction
                                (0xf << 12) | ((x & 0xf) << 8) | 0x65
                            };
                            segment.write_u16::<BigEndian>(instruction).unwrap()
                        }
                        _ => Err(AssemblyError::Compile(
                            format!("Unknown instruction '{}'", instruction_name),
                            line_col,
                        ))?,
                    }
                }
                _ => Err(AssemblyError::Token(
                    format!("Unexpected token '{}'", pair.as_str()),
                    pair.line_col(),
                ))?,
            }
        }

        if !segment.is_empty() {
            segments.push((segment_start, segment_line_col, segment));
        }

        /*let starts: Vec<u16> = segments.iter().map(|(start, _, _)| *start).collect();
        for (start, line_col, end) in segments
            .iter()
            .map(|(start, line_col, segment)| (start, line_col, start + segment.len() as u16))
        {
            let mut gt = starts.iter().filter(|s| end > **s);
            if let Some(greater) = gt.next() {
                return Err(AssemblyError::Compile(
                    format!(
                        "Segment starting at {:#06x} overlaps segment starting at {:#06x}",
                        start, *greater
                    ),
                    *line_col,
                ));
            }
        }*/

        let size = segments
            .iter()
            .map(|(start, _, segment)| start + segment.len() as u16)
            .max()
            .unwrap_or(0);

        if size > 0xfff {
            return Err(AssemblyError::Compile(
                "Code is larger than 4KB".into(),
                (0, 0),
            ));
        }

        let mut binary = vec![0_u8; size as usize];
        for (start, _, segment) in segments {
            binary[start as usize..(start as usize + segment.len())].clone_from_slice(&segment)
        }

        for (label, line_col, location) in unfinished_label_jumps {
            let label_loc = labels.get(label.as_str());
            if let Some(label_loc) = label_loc {
                binary[location as usize] = ((0x1 << 4) | (label_loc & 0xf00) >> 8) as u8;
                binary[location as usize + 1] = (label_loc & 0xff) as u8;
            } else {
                return Err(AssemblyError::Compile(
                    format!("Jump to undefined label '{}'", label),
                    line_col,
                ));
            }
        }

        Ok(binary)
    }
}
