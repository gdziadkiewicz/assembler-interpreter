use crate::model::{AssemblerInterpreterError, ConstOrRegister, Instruction, Label, LiteralString, LiterarlStringOrRegister, RegisterName};
use chumsky::text::{ident, keyword, whitespace};
use chumsky::prelude::*;

fn i64_parser() -> impl Parser<char, i64, Error = Simple<char>> {
    // Optional sign parser for positive or negative numbers
    let sign = just('-').to(-1).or(just('+').to(1)).or_not().map(|s| s.unwrap_or(1));

    // Sequence of digits parser
    let digits = text::int::<char, Simple<char>>(10);

    // Combine sign and digits into an i64 parser
    sign.then(digits)
        .map(|(sign, number_str)| sign * number_str.parse::<i64>().unwrap())
        .padded() // Skip optional leading/trailing spaces
}


fn parser<'a>() -> impl Parser<&'a str, Instruction> {
    let register_name = ident().try_map(|s: &str, span| RegisterName::new(s).map_err(|e| Simple::custom(span, format!("{}", e))));
    let const_or_register_name = ident().map(|s: &str| ConstOrRegister::new(s).unwrap());
    let label = ident().map(|s: &str| Label::new(s).unwrap());

    choice((
        keyword("mov").ignore_then(register_name).then_ignore(whitespace()).then(const_or_register_name).map(|(x, y)| Instruction::Mov(x, y)),
        keyword("inc").ignore_then(register_name).map(Instruction::Inc),
        keyword("dec").ignore_then(register_name).map(Instruction::Dec),
        keyword("add").ignore_then(register_name).then_ignore(whitespace()).then(const_or_register_name).map(|(x, y)| Instruction::Add(x, y)),
        keyword("sub").ignore_then(register_name).then_ignore(whitespace()).then(const_or_register_name).map(|(x, y)| Instruction::Sub(x, y)),
        keyword("mul").ignore_then(register_name).then_ignore(whitespace()).then(const_or_register_name).map(|(x, y)| Instruction::Mul(x, y)),
        keyword("div").ignore_then(register_name).then_ignore(whitespace()).then(const_or_register_name).map(|(x, y)| Instruction::Div(x, y)),
        keyword("jmp").ignore_then(label).map(Instruction::Jmp),
        keyword("cmp").ignore_then(const_or_register_name).then_ignore(whitespace()).then(const_or_register_name).map(|(x, y)| Instruction::Cmp(x, y)),
        keyword("jne").ignore_then(label).map(Instruction::Jne),
        keyword("je").ignore_then(label).map(Instruction::Je),
        keyword("jge").ignore_then(label).map(Instruction::Jge),
        keyword("jg").ignore_then(label).map(Instruction::Jg),
        keyword("jle").ignore_then(label).map(Instruction::Jle),
        keyword("jl").ignore_then(label).map(Instruction::Jl),
        keyword("call").ignore_then(label).map(Instruction::Call),
        keyword("ret").to(Instruction::Ret),
        keyword("msg").ignore_then(text::ident().repeated()).map(|args| Instruction::Msg(parse_msg_args(&args.join(" ")).unwrap())),
        keyword("end").to(Instruction::End),
        ident().then_ignore(just(":")).map(|s: &str| Instruction::Label(Label::new(s).unwrap())),
    ))
}

impl TryFrom<&str> for Instruction {
    type Error = AssemblerInterpreterError;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        //TODO Replace with approach that does care about missing comas
        let splited_and_trimmed_s = s
            .split_whitespace()
            .map(|x| x.trim_end_matches(','))
            .take_while(|x| !x.starts_with(";")) // cut off comments
            .collect::<Vec<&str>>();
        match &splited_and_trimmed_s[..] {
            ["mov", x, y] => {
                let x = RegisterName::new(x)?;
                let y = ConstOrRegister::new(y)?;
                Ok(Instruction::Mov(x, y))
            }
            ["inc", x] => {
                let x = RegisterName::new(x)?;
                Ok(Instruction::Inc(x))
            }
            ["dec", x] => {
                let x = RegisterName::new(x)?;
                Ok(Instruction::Dec(x))
            }
            ["add", x, y] => {
                let x = RegisterName::new(x)?;
                let y = ConstOrRegister::new(y)?;
                Ok(Instruction::Add(x, y))
            }
            ["sub", x, y] => {
                let x = RegisterName::new(x)?;
                let y = ConstOrRegister::new(y)?;
                Ok(Instruction::Sub(x, y))
            }
            ["mul", x, y] => {
                let x = RegisterName::new(x)?;
                let y = ConstOrRegister::new(y)?;
                Ok(Instruction::Mul(x, y))
            }
            ["div", x, y] => {
                let x = RegisterName::new(x)?;
                let y = ConstOrRegister::new(y)?;
                Ok(Instruction::Div(x, y))
            }
            ["jmp", lbl] => {
                let lbl: Label = Label::new(lbl)?;
                Ok(Instruction::Jmp(lbl))
            }
            ["cmp", x, y] => {
                let x = ConstOrRegister::new(x)?;
                let y = ConstOrRegister::new(y)?;
                Ok(Instruction::Cmp(x, y))
            }
            ["jne", lbl] => {
                let lbl: Label = Label::new(lbl)?;
                Ok(Instruction::Jne(lbl))
            }
            ["je", lbl] => {
                let lbl: Label = Label::new(lbl)?;
                Ok(Instruction::Je(lbl))
            }
            ["jge", lbl] => {
                let lbl: Label = Label::new(lbl)?;
                Ok(Instruction::Jge(lbl))
            }
            ["jg", lbl] => {
                let lbl: Label = Label::new(lbl)?;
                Ok(Instruction::Jg(lbl))
            }
            ["jle", lbl] => {
                let lbl: Label = Label::new(lbl)?;
                Ok(Instruction::Jle(lbl))
            }
            ["jl", lbl] => {
                let lbl: Label = Label::new(lbl)?;
                Ok(Instruction::Jl(lbl))
            }
            ["call", lbl] => {
                let lbl: Label = Label::new(lbl)?;
                Ok(Instruction::Call(lbl))
            }
            ["ret"] => Ok(Instruction::Ret),
            ["msg", ..] => {
                let i = s.find("msg").unwrap();
                let args = &s[i + 3..];
                let args = parse_msg_args(args)?;
                Ok(Instruction::Msg(args))
            }
            ["end"] => Ok(Instruction::End),
            [] => Ok(Instruction::NoOp),
            [s] if s.ends_with(":") => {
                let label = Label::new(&s[..s.len() - 1])?;
                Ok(Instruction::Label(label))
            }
            _ => Err(Self::Error::InvalidInstruction {
                instruction: s.to_string(),
            }),
        }
    }
}

enum MsgArgsParserStateMachine<'a> {
    Next {
        args: &'a mut Vec<LiterarlStringOrRegister>,
    },
    InString {
        args: &'a mut Vec<LiterarlStringOrRegister>,
        bufor: String,
    },
    Temporary {
        args: &'a mut Vec<LiterarlStringOrRegister>,
    },
    InRegister {
        args: &'a mut Vec<LiterarlStringOrRegister>,
        bufor: String,
    },
    WaitingForEnd {
        args: &'a mut Vec<LiterarlStringOrRegister>,
    },
    End {
        args: &'a mut Vec<LiterarlStringOrRegister>,
    },
}

// Can't use parsers combinator libs in CodeWars so I have writen a state machine to parse msg arguments
pub fn parse_msg_args(s: &str) -> Result<Vec<LiterarlStringOrRegister>, AssemblerInterpreterError> {
    let mut results = Vec::new();
    let sm = s.chars().chain(vec!['\0']).try_fold(
        MsgArgsParserStateMachine::Next { args: &mut results },
        |state, c| match state {
            MsgArgsParserStateMachine::Next { args } => match c {
                '\'' => Ok(MsgArgsParserStateMachine::InString {
                    args,
                    bufor: String::new(),
                }),
                ' ' => Ok(MsgArgsParserStateMachine::Next { args }),
                ';' | '\0' => Err(AssemblerInterpreterError::InvalidStringLiteralOrRegister {
                    candidate: c.to_string(),
                }),
                c => Ok(MsgArgsParserStateMachine::InRegister {
                    args,
                    bufor: c.to_string(),
                }),
            },
            MsgArgsParserStateMachine::InString { args, mut bufor } => match c {
                '\'' => {
                    args.push(LiterarlStringOrRegister::S(LiteralString::new(&bufor)));
                    Ok(MsgArgsParserStateMachine::Temporary { args })
                }
                '\0' => Err(AssemblerInterpreterError::InvalidStringLiteralOrRegister {
                    candidate: c.to_string(),
                }),
                c => {
                    bufor.push(c);
                    Ok(MsgArgsParserStateMachine::InString { args, bufor })
                }
            },
            MsgArgsParserStateMachine::Temporary { args } => match c {
                ',' => Ok(MsgArgsParserStateMachine::Next { args }),
                ' ' => Ok(MsgArgsParserStateMachine::Temporary { args }),
                ';' | '\0' => Ok(MsgArgsParserStateMachine::End { args }),
                c => Err(AssemblerInterpreterError::InvalidStringLiteralOrRegister {
                    candidate: c.to_string(),
                }),
            },
            MsgArgsParserStateMachine::InRegister { args, mut bufor } => match c {
                ',' => {
                    args.push(LiterarlStringOrRegister::R(RegisterName::new(&bufor)?));
                    Ok(MsgArgsParserStateMachine::Next { args })
                }
                ';' | '\0' => {
                    args.push(LiterarlStringOrRegister::R(RegisterName::new(&bufor)?));
                    Ok(MsgArgsParserStateMachine::End { args })
                }
                ' ' => {
                    args.push(LiterarlStringOrRegister::R(RegisterName::new(&bufor)?));
                    Ok(MsgArgsParserStateMachine::WaitingForEnd { args })
                }
                c => {
                    bufor.push(c);
                    Ok(MsgArgsParserStateMachine::InRegister { args, bufor })
                }
            },
            end @ MsgArgsParserStateMachine::End { .. } => Ok(end),
            MsgArgsParserStateMachine::WaitingForEnd { args } => match c {
                ' ' => Ok(MsgArgsParserStateMachine::WaitingForEnd { args }),
                ';' | '\0' => Ok(MsgArgsParserStateMachine::End { args }),
                c => Err(AssemblerInterpreterError::InvalidStringLiteralOrRegister {
                    candidate: c.to_string(),
                }),
            },
        },
    )?;

    match sm {
        MsgArgsParserStateMachine::End { .. } => Ok(results),
        _ => Err(AssemblerInterpreterError::InvalidStringLiteralOrRegister {
            candidate: s.to_string(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_case::test_case;
    use assert2::assert;

    #[test_case("123", 123; "positive number")]
    #[test_case("+456", 456; "positive number with plus sign")]
    #[test_case("-789", -789; "negative number")]
    #[test_case("  123  ", 123; "number with leading/trailing spaces")]
    #[test_case("  -456  ", -456; "negative number with leading/trailing spaces")]
    #[test_case("0", 0; "zero")]
    #[test_case("+0", 0; "zero with plus sign")]
    #[test_case("-0", 0; "zero with minus sign")]
    #[test_case("9223372036854775807", 9223372036854775807; "maximum i64 value")]
    #[test_case("-9223372036854775808", -9223372036854775808; "minimum i64 value")]
    fn test_i64_parser(input: &str, expected: i64) {
        let parser = i64_parser();
        assert!(parser.parse(input).unwrap() == expected);
    }

    #[test_case("9223372036854775808"; "number larger than i64")]
    #[test_case("-9223372036854775809"; "number smaller than i64")]
    fn test_i64_parser_errors(input: &str) {
        let parser = i64_parser();
        assert!(parser.parse(input).is_err() == true);
    }
}