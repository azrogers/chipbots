use chipbots_assembler::{AssemblyError, ChipAssembler};
use chipbots_vm::vm::{ExecutionResult, VirtualMachine};

#[test]
pub fn add() -> Result<(), AssemblyError> {
    let binary = ChipAssembler::assemble("add v0, 1")?;
    assert!(binary[0] == 0b0111_0000);
    assert!(binary[1] == 0b0000_0001);
    Ok(())
}

#[test]
pub fn fibonacci() -> Result<(), anyhow::Error> {
    let binary = ChipAssembler::assemble(
        "
		%entrypoint
		mov v0, 0
		mov v1, 1
		mov i, 0xf00
		loop:
		save v0
		sneq v2, 13
		jmp end
		mov v4, v1
		add v1, v0
		mov v0, v4
		add v2, 1
		jmp loop
		%location 0x400
		end:
		halt",
    )?;

    let mut vm = VirtualMachine::default();

    // copy binary to vm
    vm.memcpy(&binary, 0x0);

    loop {
        let result = vm.step()?;
        if result == ExecutionResult::Exit {
            break;
        }
        println!("{}, pc: {:#06x}", result, vm.reg.pc);
        assert!(result == ExecutionResult::Success);
    }

    assert!(vm.ram[0xf00] == 0);
    assert!(vm.ram[0xf01] == 1);
    assert!(vm.ram[0xf02] == 1);
    assert!(vm.ram[0xf03] == 2);
    assert!(vm.ram[0xf04] == 3);
    assert!(vm.ram[0xf05] == 5);
    assert!(vm.ram[0xf06] == 8);
    assert!(vm.ram[0xf07] == 13);
    assert!(vm.ram[0xf08] == 21);
    assert!(vm.ram[0xf09] == 34);
    assert!(vm.ram[0xf0a] == 55);
    assert!(vm.ram[0xf0b] == 89);
    assert!(vm.ram[0xf0c] == 144);
    assert!(vm.ram[0xf0d] == 233);
    Ok(())
}
