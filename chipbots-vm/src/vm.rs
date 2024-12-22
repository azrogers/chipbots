use std::fmt::Display;

use anyhow::{Error, Result};
use bitmatch::bitmatch;
use rand::Rng;

use crate::memory::Memory;

const ENTRY_POINT: u16 = 0x200;
const STACK_END: usize = 0xf;
const MAX_MEM: u16 = 0xfff;

#[derive(PartialEq)]
pub enum ExecutionResult {
    Success,
    Exit,
    UnknownInstruction(u16),
    StackOverflow,
    /// Instruction not supported by this environment, but should be ignored.
    /// This is things like graphics and sound instructions.
    Unsupported,
    /// Attempted to read or write past end of memory
    MemoryOverflow,
}

impl Display for ExecutionResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Success => write!(f, "Success"),
            Self::Exit => write!(f, "Exit"),
            Self::UnknownInstruction(v) => write!(f, "Unknown instruction: {:#06x}", v),
            Self::StackOverflow => write!(f, "Stack Overflow"),
            Self::Unsupported => write!(f, "Unsupported Instruction"),
            Self::MemoryOverflow => write!(f, "Memory Overflow"),
        }
    }
}

pub struct Registers {
    /// Program counter
    pub pc: u16,
    /// Current index of the stack
    /// Only 16 items are allowed in the stack
    pub sp: usize,
    /// V0-VF registers
    pub v: [u8; 16],
    /// I register
    pub i: u16,
}

pub struct VirtualMachine {
    pub ram: Memory<0xFFF>,
    pub reg: Registers,
    pub stack: [u16; 16],
}

impl Default for VirtualMachine {
    fn default() -> Self {
        VirtualMachine {
            ram: Memory::default(),
            reg: Registers {
                pc: ENTRY_POINT,
                sp: 0x0,
                v: [0; 16],
                i: 0,
            },
            stack: [0; 16],
        }
    }
}

impl VirtualMachine {
    #[bitmatch]
    pub fn step(self: &mut VirtualMachine) -> Result<ExecutionResult> {
        if self.reg.pc >= 0xfff {
            return Ok(ExecutionResult::MemoryOverflow);
        }

        let instruction = self.ram.next_instruction(&mut self.reg.pc)?;
        #[bitmatch]
        match instruction {
            // 00CN - scroll display N lines down
            "0000_0000_1100_????" => Ok(ExecutionResult::Unsupported),
            // 00DN - scroll display N lines up (XO-CHIP)
            "0000_0000_1101_????" => Ok(ExecutionResult::Unsupported),
            // 00E0 - clear display
            "0000_0000_1110_0000" => Ok(ExecutionResult::Unsupported),
            // 00EE - return from subroutine
            "0000_0000_1110_1110" => {
                if self.reg.sp == 0x0 {
                    // return at end of stack - equivalent to exit
                    return Ok(ExecutionResult::Exit);
                }

                self.reg.pc = self.stack[self.reg.sp];
                self.reg.sp -= 1;
                Ok(ExecutionResult::Success)
            }
            // 00FB - scroll display 4 pixels right
            "0000_0000_1111_1011" => Ok(ExecutionResult::Unsupported),
            // 00FC - scroll display 4 pixels left
            "0000_0000_1111_1100" => Ok(ExecutionResult::Unsupported),
            // 00FD - exit chip interpreter
            "0000_0000_1111_1101" => Ok(ExecutionResult::Exit),
            // 00FE - disable extended screen mode
            "0000_0000_1111_1110" => Ok(ExecutionResult::Unsupported),
            // 00FF - enable extended screen mode
            "0000_0000_1111_1111" => Ok(ExecutionResult::Unsupported),
            // 1NNN - jump to NNN
            "0001_nnnn_nnnn_nnnn" => {
                self.reg.pc = n;
                Ok(ExecutionResult::Success)
            }
            // 2NNN - call subroutine at NNN
            "0010_nnnn_nnnn_nnnn" => {
                if self.reg.sp == STACK_END {
                    return Ok(ExecutionResult::StackOverflow);
                }

                self.stack[self.reg.sp] = self.reg.pc;
                self.reg.sp += 1;
                self.reg.pc = n;
                Ok(ExecutionResult::Success)
            }
            // 3XKK - skip next instruction if VX == KK
            "0011_xxxx_kkkk_kkkk" => {
                if self.reg.v[x as usize] == k as u8 {
                    self.reg.pc += 2;
                }
                Ok(ExecutionResult::Success)
            }
            // 4XKK - skip next instruction if VX != KK
            "0100_xxxx_kkkk_kkkk" => {
                if self.reg.v[x as usize] != k as u8 {
                    self.reg.pc += 2;
                }

                Ok(ExecutionResult::Success)
            }
            // 5xy0 - skip next instruction if VX == VY
            "0101_xxxx_yyyy_0000" => {
                if self.reg.v[x as usize] == self.reg.v[y as usize] {
                    self.reg.pc += 2;
                }

                Ok(ExecutionResult::Success)
            }
            // 5xy2 - save VX..VY to memory starting at I (XO-CHIP)
            "0101_xxxx_yyyy_0010" => {
                let dist = u16::max(x, y) - u16::min(x, y);
                if self.reg.i > (MAX_MEM - dist) {
                    return Ok(ExecutionResult::MemoryOverflow);
                }

                for (counter, i) in (0_u16..).zip(x..=y) {
                    self.ram[self.reg.i + counter] = self.reg.v[i as usize];
                }

                Ok(ExecutionResult::Success)
            }
            // 5xy3 - load VX..VY from memory starting at I (XO-CHIP)
            "0101_xxxx_yyyy_0011" => {
                let dist = u16::max(x, y) - u16::min(x, y);
                if self.reg.i > (MAX_MEM - dist) {
                    return Ok(ExecutionResult::MemoryOverflow);
                }

                for (counter, i) in (0_u16..).zip(x..=y) {
                    self.reg.v[i as usize] = self.ram[self.reg.i + counter];
                }

                Ok(ExecutionResult::Success)
            }
            // 6xkk - set Vx = kk
            "0110_xxxx_kkkk_kkkk" => {
                self.reg.v[x as usize] = k as u8;
                Ok(ExecutionResult::Success)
            }
            // 7xkk - set VX to VX + KK
            "0111_xxxx_kkkk_kkkk" => {
                self.reg.v[x as usize] += k as u8;
                Ok(ExecutionResult::Success)
            }
            // 8xy0 - set VX = VY
            "1000_xxxx_yyyy_0000" => {
                self.reg.v[x as usize] = self.reg.v[y as usize];
                Ok(ExecutionResult::Success)
            }
            // 8xy1 - set VX to VX | VY
            "1000_xxxx_yyyy_0001" => {
                self.reg.v[x as usize] |= self.reg.v[y as usize];
                Ok(ExecutionResult::Success)
            }
            // 8xy2 - set VX to VX & VY
            "1000_xxxx_yyyy_0010" => {
                self.reg.v[x as usize] &= self.reg.v[y as usize];
                Ok(ExecutionResult::Success)
            }
            // 8xy3 - set VX to VX ^ VY
            "1000_xxxx_yyyy_0011" => {
                self.reg.v[x as usize] ^= self.reg.v[y as usize];
                Ok(ExecutionResult::Success)
            }
            // 8xy4 - set VX to VX + VY, set VF = carry
            "1000_xxxx_yyyy_0100" => {
                let num = self.reg.v[x as usize] as u16 + self.reg.v[y as usize] as u16;
                if num > 0xff {
                    self.reg.v[0xf] = 1;
                }
                self.reg.v[x as usize] = num as u8;
                Ok(ExecutionResult::Success)
            }
            // 8xy5 - set VX to VX - VY, set VF = NOT borrow
            "1000_xxxx_yyyy_0101" => {
                if self.reg.v[x as usize] > self.reg.v[y as usize] {
                    self.reg.v[0xf] = 1;
                } else {
                    self.reg.v[0xf] = 0;
                }

                self.reg.v[x as usize] -= self.reg.v[y as usize];
                Ok(ExecutionResult::Success)
            }
            // 8xy6 - shift VY right one bit and store in VX, store that bit in VF
            "1000_xxxx_yyyy_0110" => {
                self.reg.v[0xf] = self.reg.v[x as usize] & 0x1;
                self.reg.v[x as usize] = self.reg.v[y as usize] >> 1;
                Ok(ExecutionResult::Success)
            }
            // 8xy7 - set VX to VY - VX, set VF = NOT borrow
            "1000_xxxx_yyyy_0111" => {
                if self.reg.v[y as usize] > self.reg.v[x as usize] {
                    self.reg.v[0xf] = 1;
                } else {
                    self.reg.v[0xf] = 0;
                }

                self.reg.v[y as usize] -= self.reg.v[x as usize];
                Ok(ExecutionResult::Success)
            }
            // 8xyE - set VX to VY shifted left 1 bit, set VF = previous most significant bit
            "1000_xxxx_yyyy_1110" => {
                self.reg.v[0xf] = self.reg.v[y as usize] >> 7;
                self.reg.v[x as usize] = self.reg.v[y as usize] << 1;
                Ok(ExecutionResult::Success)
            }
            // 9xy0 - skip next instruction if VX != VY
            "1001_xxxx_yyyy_0000" => {
                if self.reg.v[x as usize] != self.reg.v[y as usize] {
                    self.reg.pc += 2;
                }
                Ok(ExecutionResult::Success)
            }
            // Annn - set I = nnn
            "1010_nnnn_nnnn_nnnn" => {
                self.reg.i = n;
                Ok(ExecutionResult::Success)
            }
            // Bnnn - jump to location nnn + V0
            "1011_nnnn_nnnn_nnnn" => {
                self.reg.pc = n + self.reg.v[0x0] as u16;
                Ok(ExecutionResult::Success)
            }
            // Cxkk - set VX = random byte & KK
            "1100_xxxx_kkkk_kkkk" => {
                let rand: u8 = rand::random();
                self.reg.v[x as usize] = rand & k as u8;
                Ok(ExecutionResult::Success)
            }
            // Dxyn - display sprite
            "1101_????_????_????" => Ok(ExecutionResult::Unsupported),
            // Ex9E - skip next instruction if key pressed
            "1110_????_0101_1110" => Ok(ExecutionResult::Unsupported),
            // ExA1 - skip next instruction if key not pressed
            "1110_????_1010_0001" => Ok(ExecutionResult::Unsupported),
            // F000 NNNN - load I with 16-bit address NNNN (XO-CHIP)
            "1111_0000_0000_0000" => Ok(ExecutionResult::Unsupported),
            // Fn01 - select drawing planes by bitmask (XO-CHIP)
            "1111_????_0000_0001" => Ok(ExecutionResult::Unsupported),
            // F002 - store 16 bytes in audio pattern buffer starting at I
            "1111_0000_0000_0010" => Ok(ExecutionResult::Unsupported),
            // Fx07 - set VX = delay timer value
            "1111_????_0000_0111" => Ok(ExecutionResult::Unsupported),
            // Fx0A - wait for key press, store value in VX
            "1111_????_0000_1010" => Ok(ExecutionResult::Unsupported),
            // Fx15 - set delay timer = VX
            "1111_????_0001_0101" => Ok(ExecutionResult::Unsupported),
            // Fx18 - set sound timer = VX
            "1111_????_0001_1000" => Ok(ExecutionResult::Unsupported),
            // Fx1E - set I = I + VX
            "1111_xxxx_0001_1110" => {
                self.reg.i += self.reg.v[x as usize] as u16;
                Ok(ExecutionResult::Success)
            }
            // Fx29 - set I = location of sprite for digit VX
            "1111_????_0010_1001" => Ok(ExecutionResult::Unsupported),
            // Fx30 - set I = location of 10-byte font sprite
            "1111_????_0011_0000" => Ok(ExecutionResult::Unsupported),
            // Fx33 - store BCD representation of Vx in memory locations I, I+1, I+2
            "1111_xxxx_0011_0011" => {
                if self.reg.i > (MAX_MEM - 2) {
                    return Ok(ExecutionResult::MemoryOverflow);
                }

                let val = self.reg.v[x as usize];
                let hundreds = val / 100;
                let tens = val / 10 % 10;
                let ones = val % 10;
                self.ram[self.reg.i] = hundreds;
                self.ram[self.reg.i + 1] = tens;
                self.ram[self.reg.i + 2] = ones;
                Ok(ExecutionResult::Success)
            }
            // Fx3A - set pitch register to the value in VX
            "1111_xxxx_0011_1010" => Ok(ExecutionResult::Unsupported),
            // Fx55 - store registers V0 through VX in memory starting at location I
            "1111_xxxx_0101_0101" => {
                if self.reg.i > (MAX_MEM - x) {
                    return Ok(ExecutionResult::MemoryOverflow);
                }

                for i in 0..=x {
                    self.ram[self.reg.i + i] = self.reg.v[i as usize];
                }

                self.reg.i += x + 1;

                Ok(ExecutionResult::Success)
            }
            // Fx65 - read registers V0 through VX from memory starting at location i
            "1111_xxxx_0110_0101" => {
                if self.reg.i > (MAX_MEM - x) {
                    return Ok(ExecutionResult::MemoryOverflow);
                }

                for i in 0..=x {
                    self.reg.v[i as usize] = self.ram[self.reg.i + i];
                }

                self.reg.i += x + 1;

                Ok(ExecutionResult::Success)
            }
            _ => Ok(ExecutionResult::UnknownInstruction(instruction)),
        }
    }
}
