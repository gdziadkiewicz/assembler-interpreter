use std::collections::HashMap;

use crate::model::{AssemblerInterpreterError, ConstOrRegister, Instruction, Label, LiteralString, LiterarlStringOrRegister, RegisterName};

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

impl ConstOrRegister {
    fn to_value(&self, registers: &Registers) -> Result<i64, AssemblerInterpreterError> {
        match self {
            ConstOrRegister::R(r) => registers.get(r).copied(),
            ConstOrRegister::C(c) => Ok(c.0),
        }
    }
}

pub fn interpret_instructions(
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
            Instruction::Label(_) => {}
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
                if compare == std::cmp::Ordering::Greater || compare == std::cmp::Ordering::Equal {
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