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
    pub fn new(name: &str) -> Result<Self, AssemblerInterpreterError> {
        if !name.chars().all(|c| c.is_alphabetic()) {
            return Err(AssemblerInterpreterError::InvalidRegisterName {
                register_name: name.to_string(),
            });
        }
        Ok(Self(name.to_string()))
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Const(pub i64);

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
#[derive(Clone)]
pub enum ConstOrRegister {
    R(RegisterName),
    C(Const),
}
impl ConstOrRegister {
    pub fn new(rc: &str) -> Result<Self, AssemblerInterpreterError> {
        Const::new(rc)
            .map(ConstOrRegister::C)
            .or_else(|_| RegisterName::new(rc).map(ConstOrRegister::R))
            .map_err(|_| AssemblerInterpreterError::InvalidConstOrRegister {
                const_or_register: rc.to_string(),
            })
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Label(String);
impl Label {
    const RESERVED_NAMES: &[&str] = &[
        "mov", "inc", "dec", "add", "sub", "mul", "div", "label", "jmp", "cmp", "jne", "je", "jge",
        "jg", "jle", "jl", "call", "ret", "msg", "end",
    ];
    pub fn new(name: &str) -> Result<Self, AssemblerInterpreterError> {
        if Self::RESERVED_NAMES.contains(&name) {
            return Err(AssemblerInterpreterError::InvalidLabelName {
                name: name.to_string(),
            });
        }
        Ok(Self(name.to_string()))
    }
}
#[derive(Clone)]
pub struct LiteralString(pub String);
impl LiteralString {
    pub fn new(s: &str) -> Self {
        Self(s.to_string())
    }
}

#[derive(Clone)]
pub enum LiterarlStringOrRegister {
    S(LiteralString),
    R(RegisterName),
}

#[derive(Clone)]
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