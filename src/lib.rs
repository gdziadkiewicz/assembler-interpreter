use std::collections::HashMap;

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum AssemblerInterpreterError {
    InvalidInstruction { instruction: String },
    InvalidRegisterName { register_name: String },
    InvalidConst { const_candidate: String },
    InvalidConstOrRegister { const_or_register: String },
    InvalidLabelName { name: String },
    MissingLabel { name: Label },
    MissingRegister { register_name: RegisterName },
    InvalidStringLiteral { str_candidate: String },
    InvalidStringLiteralOrRegister { candidate: String },
    MissingCompare,
    EmptyCallStack,
}

impl std::fmt::Display for AssemblerInterpreterError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            AssemblerInterpreterError::InvalidInstruction { instruction } => {
                write!(f, "Invalid instruction: {}", instruction)
            }
            AssemblerInterpreterError::MissingRegister { register_name } => {
                write!(f, "Missing register: {}", register_name)
            }
            AssemblerInterpreterError::InvalidRegisterName { register_name } => {
                write!(f, "Invalid register name: {}", register_name)
            }
            AssemblerInterpreterError::InvalidConst { const_candidate } => {
                write!(f, "Invalid constant: {}", const_candidate)
            }
            AssemblerInterpreterError::InvalidConstOrRegister { const_or_register } => {
                write!(f, "Invalid constant or register: {}", const_or_register)
            }
            AssemblerInterpreterError::InvalidLabelName { name } => {
                write!(f, "Invalid label name: {}", name)
            }
            AssemblerInterpreterError::InvalidStringLiteral { str_candidate } => {
                write!(f, "Invalid string literal: {}", str_candidate)
            }
            AssemblerInterpreterError::InvalidStringLiteralOrRegister { candidate } => {
                write!(f, "Invalid string literal or register: {}", candidate)
            }
            AssemblerInterpreterError::MissingLabel { name } => {
                write!(f, "Missing label: {}", name.0)
            }
            AssemblerInterpreterError::MissingCompare => {
                write!(f, "Missing compare")
            }
            AssemblerInterpreterError::EmptyCallStack => {
                write!(f, "Empty call stack")
            }
        }
    }
}

impl std::error::Error for AssemblerInterpreterError {}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct RegisterName(String);

impl std::fmt::Display for RegisterName {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl RegisterName {
    fn new(name: &str) -> Result<Self, AssemblerInterpreterError> {
        if !name.chars().all(|c| c.is_alphabetic()) {
            return Err(AssemblerInterpreterError::InvalidRegisterName {
                register_name: name.to_string(),
            });
        }
        Ok(Self(name.to_string()))
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Const(i64);

impl Const {
    fn new(c: &str) -> Result<Self, AssemblerInterpreterError> {
        let c = c
            .parse()
            .map_err(|_| AssemblerInterpreterError::InvalidConst {
                const_candidate: c.to_string(),
            })?;
        Ok(Self(c))
    }
}
pub enum ConstOrRegister {
    R(RegisterName),
    C(Const),
}
impl ConstOrRegister {
    fn new(rc: &str) -> Result<Self, AssemblerInterpreterError> {
        Const::new(rc)
            .map(ConstOrRegister::C)
            .or_else(|_| RegisterName::new(rc).map(ConstOrRegister::R))
            .map_err(|_| AssemblerInterpreterError::InvalidConstOrRegister {
                const_or_register: rc.to_string(),
            })
    }

    fn to_value(&self, registers: &Registers) -> Result<i64, AssemblerInterpreterError> {
        match self {
            ConstOrRegister::R(r) => registers.get(r).map(|x| *x),
            ConstOrRegister::C(c) => Ok(c.0),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Label(String);
impl Label {
    const RESERVED_NAMES: &[&str] = &[
        "mov", "inc", "dec", "add", "sub", "mul", "div", "label", "jmp", "cmp", "jne", "je", "jge",
        "jg", "jle", "jl", "call", "ret", "msg", "end",
    ];
    fn new(name: &str) -> Result<Self, AssemblerInterpreterError> {
        if Self::RESERVED_NAMES.contains(&name) {
            return Err(AssemblerInterpreterError::InvalidLabelName {
                name: name.to_string(),
            });
        }
        Ok(Self(name.to_string()))
    }
}
pub struct LiteralString(String);
impl LiteralString {
    fn new(s: &str) -> Self {
        Self(s.to_string())
    }
}

pub enum LiterarlStringOrRegister {
    S(LiteralString),
    R(RegisterName),
}

pub enum Instruction {
    Mov(RegisterName, ConstOrRegister),
    Inc(RegisterName),
    Dec(RegisterName),
    Add(RegisterName, ConstOrRegister),
    Sub(RegisterName, ConstOrRegister),
    Mul(RegisterName, ConstOrRegister),
    Div(RegisterName, ConstOrRegister),
    Label(Label),
    Jmp(Label),
    Cmp(ConstOrRegister, ConstOrRegister),
    Jne(Label),
    Je(Label),
    Jge(Label),
    Jg(Label),
    Jle(Label),
    Jl(Label),
    Call(Label),
    Ret,
    Msg(Vec<LiterarlStringOrRegister>),
    End,
    NoOp,
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

pub struct Registers(HashMap<RegisterName, i64>);
impl Registers {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn get(&self, register: &RegisterName) -> Result<&i64, AssemblerInterpreterError> {
        self.0
            .get(register)
            .ok_or(AssemblerInterpreterError::MissingRegister {
                register_name: register.clone(),
            })
    }

    pub fn get_mut(
        &mut self,
        register: &RegisterName,
    ) -> Result<&mut i64, AssemblerInterpreterError> {
        self.0
            .get_mut(register)
            .ok_or(AssemblerInterpreterError::MissingRegister {
                register_name: register.clone(),
            })
    }

    pub fn insert(&mut self, register: RegisterName, value: i64) {
        self.0.insert(register, value);
    }
}

impl Default for Registers {
    fn default() -> Self {
        Self::new()
    }
}

pub struct AssemblerInterpreter {}

pub struct CallStack {
    stack: Vec<i64>,
}

impl CallStack {
    pub fn new() -> Self {
        Self { stack: vec![0] }
    }

    pub fn push(&mut self, value: i64) {
        self.stack.push(value);
    }

    pub fn pop(&mut self) -> Result<i64, AssemblerInterpreterError> {
        self.stack
            .pop()
            .ok_or(AssemblerInterpreterError::EmptyCallStack)
    }

    pub fn peek_mut(&mut self) -> Result<&mut i64, AssemblerInterpreterError> {
        self.stack
            .last_mut()
            .ok_or(AssemblerInterpreterError::EmptyCallStack)
    }

    pub fn peek(&self) -> Result<&i64, AssemblerInterpreterError> {
        self.stack
            .last()
            .ok_or(AssemblerInterpreterError::EmptyCallStack)
    }
}

impl Default for CallStack {
    fn default() -> Self {
        Self::new()
    }
}

impl AssemblerInterpreter {
    fn interpret_instructions(
        instructions: &[Instruction],
    ) -> Result<Option<String>, AssemblerInterpreterError> {
        let mut registers = Registers::new();
        let mut call_stack = CallStack::new();
        let mut compare: Option<std::cmp::Ordering> = None;
        let mut output: Option<String> = None;
        let mut has_ended = false;
        while let Some(instruction) = instructions.get(*call_stack.peek()? as usize) {
            match instruction {
                Instruction::Mov(x, y) => {
                    let value = match y {
                        ConstOrRegister::R(r) => *registers.get(r)?,
                        ConstOrRegister::C(c) => c.0,
                    };
                    registers.insert(x.clone(), value);
                }
                Instruction::Inc(register) => {
                    *registers.get_mut(register)? += 1;
                }
                Instruction::Dec(register) => {
                    *registers.get_mut(register)? -= 1;
                }
                Instruction::Cmp(x, y) => {
                    let x = x.to_value(&registers)?;
                    let y = y.to_value(&registers)?;
                    compare = Some(x.cmp(&y));
                }
                Instruction::Add(register_name, const_or_register) => {
                    let value = const_or_register.to_value(&registers)?;
                    *registers.get_mut(register_name)? += value;
                }
                Instruction::Sub(register_name, const_or_register) => {
                    let value = const_or_register.to_value(&registers)?;
                    *registers.get_mut(register_name)? -= value;
                }
                Instruction::Mul(register_name, const_or_register) => {
                    let value = const_or_register.to_value(&registers)?;
                    *registers.get_mut(register_name)? *= value;
                }
                Instruction::Div(register_name, const_or_register) => {
                    let value = const_or_register.to_value(&registers)?;
                    *registers.get_mut(register_name)? /= value;
                }
                Instruction::Label(label) => {}
                Instruction::Jmp(label) => jump(call_stack.peek_mut()?, instructions, label)?,
                Instruction::Jne(label) => {
                    let compare = compare.ok_or(AssemblerInterpreterError::MissingCompare)?;
                    if compare != std::cmp::Ordering::Equal {
                        jump(call_stack.peek_mut()?, instructions, label)?
                    }
                }
                Instruction::Je(label) => {
                    let compare = compare.ok_or(AssemblerInterpreterError::MissingCompare)?;
                    if compare == std::cmp::Ordering::Equal {
                        jump(call_stack.peek_mut()?, instructions, label)?
                    }
                }
                Instruction::Jge(label) => {
                    let compare = compare.ok_or(AssemblerInterpreterError::MissingCompare)?;
                    if compare == std::cmp::Ordering::Greater
                        || compare == std::cmp::Ordering::Equal
                    {
                        jump(call_stack.peek_mut()?, instructions, label)?
                    }
                }
                Instruction::Jg(label) => {
                    let compare = compare.ok_or(AssemblerInterpreterError::MissingCompare)?;
                    if compare == std::cmp::Ordering::Greater {
                        jump(call_stack.peek_mut()?, instructions, label)?
                    }
                }
                Instruction::Jle(label) => {
                    let compare = compare.ok_or(AssemblerInterpreterError::MissingCompare)?;
                    if compare == std::cmp::Ordering::Less || compare == std::cmp::Ordering::Equal {
                        jump(call_stack.peek_mut()?, instructions, label)?
                    }
                }
                Instruction::Jl(label) => {
                    let compare = compare.ok_or(AssemblerInterpreterError::MissingCompare)?;
                    if compare == std::cmp::Ordering::Less {
                        jump(call_stack.peek_mut()?, instructions, label)?
                    }
                }
                Instruction::Call(label) => {
                    let label_index = get_label_index(instructions, label)?;
                    call_stack.push(label_index as i64);
                }
                Instruction::Ret => {
                    call_stack.pop()?;
                }
                Instruction::Msg(args) => {
                    let mut msg = String::new();
                    for arg in args {
                        match arg {
                            LiterarlStringOrRegister::S(LiteralString(s)) => msg.push_str(s),
                            LiterarlStringOrRegister::R(register_name) => {
                                msg.push_str(&registers.get(register_name)?.to_string())
                            }
                        }
                    }
                    output = Some(msg);
                }
                Instruction::End => {
                    has_ended = true;
                    break;
                }
                Instruction::NoOp => {}
            }
            *call_stack.peek_mut()? += 1;
        }
        if has_ended {
            Ok(output)
        } else {
            Ok(None)
        }
    }

    pub fn interpret_to_result(input: &str) -> Result<Option<String>, AssemblerInterpreterError> {
        let instructions = input
            .lines()
            .filter(|s| !s.is_empty())
            .map(Instruction::try_from)
            .collect::<Result<Vec<Instruction>, AssemblerInterpreterError>>()?;
        Self::interpret_instructions(&instructions)
    }

    pub fn interpret(input: &str) -> Option<String> {
        Self::interpret_to_result(input).unwrap()
    }
}

fn jump(
    ip: &mut i64,
    instructions: &[Instruction],
    label: &Label,
) -> Result<(), AssemblerInterpreterError> {
    let label_index = get_label_index(instructions, label)?;
    *ip = label_index as i64 - 1;
    Ok(())
}

fn get_label_index(
    instructions: &[Instruction],
    label: &Label,
) -> Result<usize, AssemblerInterpreterError> {
    let label_index = instructions
        .iter()
        .position(|i| matches!(i, Instruction::Label(l) if l == label));
    label_index.ok_or_else(|| AssemblerInterpreterError::MissingLabel {
        name: label.clone(),
    })
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use assert2::assert;

    #[test]
    fn test_simple_program_1() {
        let program = r#"
    ; My first program
    mov  a, 5
    inc  a
    call function
    msg  '(5+1)/2 = ', a    ; output message
    end

    function:
        div  a, 2
        ret
    "#;
        let expected = Some(String::from("(5+1)/2 = 3"));
        assert!(AssemblerInterpreter::interpret_to_result(program).as_ref() == Ok(&expected));
    }

    #[test]
    fn test_simple_program_2() {
        let program = r#"
    mov   a, 5
    mov   b, a
    mov   c, a
    call  proc_fact
    call  print
    end

    proc_fact:
        dec   b
        mul   c, b
        cmp   b, 1
        jne   proc_fact
        ret

    print:
        msg   a, '! = ', c ; output text
        ret
    "#;
        let expected = Some(String::from("5! = 120"));
        assert!(AssemblerInterpreter::interpret_to_result(program).as_ref() == Ok(&expected));
    }

    #[test]
    fn test_simple_program_3() {
        let program = r#"
    mov   a, 8            ; value
    mov   b, 0            ; next
    mov   c, 0            ; counter
    mov   d, 0            ; first
    mov   e, 1            ; second
    call  proc_fib
    call  print
    end

    proc_fib:
        cmp   c, 2
        jl    func_0
        mov   b, d
        add   b, e
        mov   d, e
        mov   e, b
        inc   c
        cmp   c, a
        jle   proc_fib
        ret

    func_0:
        mov   b, c
        inc   c
        jmp   proc_fib

    print:
        msg   'Term ', a, ' of Fibonacci series is: ', b        ; output text
        ret
    "#;
        let expected = Some(String::from("Term 8 of Fibonacci series is: 21"));
        assert!(AssemblerInterpreter::interpret_to_result(program).as_ref() == Ok(&expected));
    }

    #[test]
    fn test_simple_program_4() {
        let program = r#"
    mov   a, 11           ; value1
    mov   b, 3            ; value2
    call  mod_func
    msg   'mod(', a, ', ', b, ') = ', d        ; output
    end

    ; Mod function
    mod_func:
        mov   c, a        ; temp1
        div   c, b
        mul   c, b
        mov   d, a        ; temp2
        sub   d, c
        ret
    "#;
        let expected = Some(String::from("mod(11, 3) = 2"));
        assert!(AssemblerInterpreter::interpret_to_result(program).as_ref() == Ok(&expected));
    }

    #[test]
    fn test_simple_program_5() {
        let program = r#"
    mov   a, 81         ; value1
    mov   b, 153        ; value2
    call  init
    call  proc_gcd
    call  print
    end

    proc_gcd:
        cmp   c, d
        jne   loop
        ret

    loop:
        cmp   c, d
        jg    a_bigger
        jmp   b_bigger

    a_bigger:
        sub   c, d
        jmp   proc_gcd

    b_bigger:
        sub   d, c
        jmp   proc_gcd

    init:
        cmp   a, 0
        jl    a_abs
        cmp   b, 0
        jl    b_abs
        mov   c, a            ; temp1
        mov   d, b            ; temp2
        ret

    a_abs:
        mul   a, -1
        jmp   init

    b_abs:
        mul   b, -1
        jmp   init

    print:
        msg   'gcd(', a, ', ', b, ') = ', c
        ret
    "#;
        let expected = Some(String::from("gcd(81, 153) = 9"));
        assert!(AssemblerInterpreter::interpret_to_result(program).as_ref() == Ok(&expected));
    }

    #[test]
    fn test_simple_program_6() {
        let program = r#"
    call  func1
    call  print
    end

    func1:
        call  func2
        ret

    func2:
        ret

    print:
        msg 'This program should return null'
    "#;
        let expected = None;
        assert!(AssemblerInterpreter::interpret_to_result(program).as_ref() == Ok(&expected));
    }

    #[test]
    fn test_simple_program_7() {
        let program = r#"
    mov   a, 2            ; value1
    mov   b, 10           ; value2
    mov   c, a            ; temp1
    mov   d, b            ; temp2
    call  proc_func
    call  print
    end

    proc_func:
        cmp   d, 1
        je    continue
        mul   c, a
        dec   d
        call  proc_func

    continue:
        ret

    print:
        msg a, '^', b, ' = ', c
        ret
    "#;
        let expected = Some(String::from("2^10 = 1024"));
        assert!(AssemblerInterpreter::interpret_to_result(program).as_ref() == Ok(&expected));
    }
}
