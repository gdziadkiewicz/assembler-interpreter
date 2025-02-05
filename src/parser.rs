use crate::model::{AssemblerInterpreterError, ConstOrRegister, Instruction, Label, LiteralString, LiterarlStringOrRegister, RegisterName};

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