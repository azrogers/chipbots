use anyhow::{Error, Result};
use chipbots_vm_macros::instruction_set;
use zerocopy::FromZeros;

use crate::memory::Memory;

const ENTRY_POINT: u16 = 0x80;

pub enum InstructionArgumentInfo {
    Register,
    Constant,
    Address,
}

pub struct InstructionInfo {
    byte: u8,
    name: &'static str,
    args: &'static [InstructionArgumentInfo],
}

/// Four 32-bit registers
/// EAX, EBX, ECX, EDX
/// The lower 16-bits of each register is also addressable
/// AX, BX, CX, DX
/// The high and low bytes of each 16-bit register is addressable as H and L
/// AH, AL, BH, BL, CH, CL, DH, DL
///
/// These registers can be addressed using four bits.
/// Top two bits:
///  - 00 - A
///  - 01 - B
///  - 10 - C
///  - 11 - D
/// Bottom two bits:
///  - 00 - E*X
///  - 01 - *X
///  - 10 - *H
///  - 01 - *L
///
/// This means an instruction like `OPCODE REGISTER REGISTER` can be written with two bytes.

#[derive(FromZeros)]
union Register {
    u: u32,
    i: i32,
    f: f32,
    s: [u16; 2],
}

impl Default for Register {
    fn default() -> Self {
        Register { i: 0 }
    }
}

#[derive(Default)]
#[repr(C)]
struct Registers {
    a: Register,
    b: Register,
    c: Register,
    d: Register,
    flags: u16,
}

pub enum ExecutionResult {
    Success,
    Halt,
    UnknownOpcode(u8),
}

pub struct VirtualMachine<const N: usize> {
    ram: Memory<N>,
    /// Program Counter
    pc: u16,
    /// Stack Pointer
    sp: u16,
    /// Four 32-bit Registers + Flags
    reg: Registers,
}

impl<const N: usize> Default for VirtualMachine<N> {
    fn default() -> Self {
        VirtualMachine {
            ram: Memory::default(),
            pc: ENTRY_POINT,
            sp: N as u16,
            reg: Registers::default(),
        }
    }
}

impl<const N: usize> VirtualMachine<N> {
    pub fn step(self: &mut VirtualMachine<N>) -> Result<ExecutionResult> {
        let opcode = self.ram.next::<u8>(&mut self.pc)?;
        self.step_internal(opcode)
    }

    fn register_for<'vm>(self: &'vm mut VirtualMachine<N>, selector: u8) -> &'vm mut Register {
        let upper = selector & 0xc >> 4;
        match upper {
            0x00 => &mut self.reg.a,
            0x01 => &mut self.reg.b,
            0x02 => &mut self.reg.c,
            _ => &mut self.reg.d,
        }
    }

    fn register_mask_for(selector: u8) -> u32 {
        match selector & 0x3 {
            0x00 => 0xFFFFFFFF,
            0x01 => 0xFFFF,
            0x02 => 0xFF00,
            _ => 0xFF,
        }
    }
}

instruction_set! {
    VirtualMachine,
    InstructionInfo,
    INSTRUCTIONS,
    ExecutionResult,
    Ok(ExecutionResult::UnknownOpcode(opcode)),
    { 0x00, "nop", [], { Ok(ExecutionResult::Success) } },
    { 0x01, "add", [InstructionArgumentInfo::Register, InstructionArgumentInfo::Register], {
        let registers = self.ram.next::<u8>(&mut self.pc)?;
        let from = (registers >> 4) & 0xF;
        let to = registers & 0xF;
        let from_reg = self.register_for(from);
        let to_reg = self.register_for(to);

        Ok(ExecutionResult::Success)
    } }
}
