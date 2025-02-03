use std::{
    collections::HashMap,
    ops::{AddAssign, SubAssign},
};

#[derive(Debug, Hash, PartialEq, Eq)]
pub enum AssemblerInterpreterError {
    InvalidInstruction { instruction: String },
    InvalidRegisterName { register_name: String },
    InvalidConst { const_candidate: String },
    InvalidConstOrRegister { const_or_register: String },
    MissingRegister { register_name: RegisterName },
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
}

pub enum Instruction {
    Mov(RegisterName, ConstOrRegister),
    Inc(RegisterName),
    Dec(RegisterName),
    Jnz(ConstOrRegister, ConstOrRegister),
}

impl TryFrom<&str> for Instruction {
    type Error = AssemblerInterpreterError;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        let splited_s = s.split_whitespace().collect::<Vec<&str>>();
        match &splited_s[..] {
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
            ["jnz", x, y] => {
                let x = ConstOrRegister::new(x)?;
                let y = ConstOrRegister::new(y)?;
                Ok(Instruction::Jnz(x, y))
            }
            _ => Err(Self::Error::InvalidInstruction {
                instruction: s.to_string(),
            }),
        }
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

fn run_on_registers(
    instructions: &[Instruction],
    registers: &mut Registers,
) -> Result<(), AssemblerInterpreterError> {
    let mut ip = 0i64;
    while let Some(instruction) = instructions.get(ip as usize) {
        match instruction {
            Instruction::Mov(x, y) => {
                let value = match y {
                    ConstOrRegister::R(r) => *registers.get(r)?,
                    ConstOrRegister::C(c) => c.0,
                };
                registers.insert(x.clone(), value);
            }
            Instruction::Inc(register) => {
                registers.get_mut(register)?.add_assign(1);
            }
            Instruction::Dec(register) => {
                registers.get_mut(register)?.sub_assign(1);
            }
            Instruction::Jnz(x, y) => match x {
                ConstOrRegister::R(r) if registers.get(r)? == &0 => {}
                ConstOrRegister::C(Const(0)) => {}
                _ => {
                    let step = match y {
                        ConstOrRegister::R(r) => registers.get(r)?,
                        ConstOrRegister::C(c) => &c.0,
                    };
                    ip += step - 1;
                }
            },
        }
        ip += 1;
    }
    Ok(())
}

fn run(instructions: &[Instruction]) -> Result<Registers, AssemblerInterpreterError> {
    let mut registers = Registers::new();
    run_on_registers(instructions, &mut registers)?;
    Ok(registers)
}

pub fn parse_and_run_assembler_code(
    program: &[&str],
) -> Result<Registers, AssemblerInterpreterError> {
    let instructions = program
        .iter()
        .map(|s| Instruction::try_from(*s))
        .collect::<Result<Vec<Instruction>, AssemblerInterpreterError>>()?;
    run(&instructions)
}

fn simple_assembler(program: Vec<&str>) -> HashMap<String, i64> {
    let registers = parse_and_run_assembler_code(&program).unwrap().0;
    unsafe { std::mem::transmute(registers) }
}

pub struct AssemblerInterpreter {
}

impl AssemblerInterpreter {
    pub fn interpret(input: &str) -> Option<String> {
        unimplemented!();
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn simple_test() {
        let simple_programs = &[
            "\n; My first program\nmov  a, 5\ninc  a\ncall function\nmsg  '(5+1)/2 = ', a    ; output message\nend\n\nfunction:\n    div  a, 2\n    ret\n",
            "\nmov   a, 5\nmov   b, a\nmov   c, a\ncall  proc_fact\ncall  print\nend\n\nproc_fact:\n    dec   b\n    mul   c, b\n    cmp   b, 1\n    jne   proc_fact\n    ret\n\nprint:\n    msg   a, '! = ', c ; output text\n    ret\n",
            "\nmov   a, 8            ; value\nmov   b, 0            ; next\nmov   c, 0            ; counter\nmov   d, 0            ; first\nmov   e, 1            ; second\ncall  proc_fib\ncall  print\nend\n\nproc_fib:\n    cmp   c, 2\n    jl    func_0\n    mov   b, d\n    add   b, e\n    mov   d, e\n    mov   e, b\n    inc   c\n    cmp   c, a\n    jle   proc_fib\n    ret\n\nfunc_0:\n    mov   b, c\n    inc   c\n    jmp   proc_fib\n\nprint:\n    msg   'Term ', a, ' of Fibonacci series is: ', b        ; output text\n    ret\n",
            "\nmov   a, 11           ; value1\nmov   b, 3            ; value2\ncall  mod_func\nmsg   'mod(', a, ', ', b, ') = ', d        ; output\nend\n\n; Mod function\nmod_func:\n    mov   c, a        ; temp1\n    div   c, b\n    mul   c, b\n    mov   d, a        ; temp2\n    sub   d, c\n    ret\n",
            "\nmov   a, 81         ; value1\nmov   b, 153        ; value2\ncall  init\ncall  proc_gcd\ncall  print\nend\n\nproc_gcd:\n    cmp   c, d\n    jne   loop\n    ret\n\nloop:\n    cmp   c, d\n    jg    a_bigger\n    jmp   b_bigger\n\na_bigger:\n    sub   c, d\n    jmp   proc_gcd\n\nb_bigger:\n    sub   d, c\n    jmp   proc_gcd\n\ninit:\n    cmp   a, 0\n    jl    a_abs\n    cmp   b, 0\n    jl    b_abs\n    mov   c, a            ; temp1\n    mov   d, b            ; temp2\n    ret\n\na_abs:\n    mul   a, -1\n    jmp   init\n\nb_abs:\n    mul   b, -1\n    jmp   init\n\nprint:\n    msg   'gcd(', a, ', ', b, ') = ', c\n    ret\n",
            "\ncall  func1\ncall  print\nend\n\nfunc1:\n    call  func2\n    ret\n\nfunc2:\n    ret\n\nprint:\n    msg 'This program should return null'\n",
            "\nmov   a, 2            ; value1\nmov   b, 10           ; value2\nmov   c, a            ; temp1\nmov   d, b            ; temp2\ncall  proc_func\ncall  print\nend\n\nproc_func:\n    cmp   d, 1\n    je    continue\n    mul   c, a\n    dec   d\n    call  proc_func\n\ncontinue:\n    ret\n\nprint:\n    msg a, '^', b, ' = ', c\n    ret\n"];

        let expected = &[
            Some(String::from("(5+1)/2 = 3")),
            Some(String::from("5! = 120")),
            Some(String::from("Term 8 of Fibonacci series is: 21")),
            Some(String::from("mod(11, 3) = 2")),
            Some(String::from("gcd(81, 153) = 9")),
            None,
            Some(String::from("2^10 = 1024"))];

        for (prg, exp) in simple_programs.iter().zip(expected) {
            let actual = AssemblerInterpreter::interpret(*prg);
            assert_eq!(actual, *exp);
        }
    }
}
