use chipbots_vm::vm::{ExecutionResult, VirtualMachine};

#[test]
fn add_instruction() -> anyhow::Result<()> {
    let mut vm = VirtualMachine::default();
    // add 1 to register V0
    vm.ram[0x200] = 0b0111_0000;
    vm.ram[0x201] = 0b0000_0001;
    let result = vm.step()?;
    println!("{}", result);
    assert!(result == ExecutionResult::Success);
    assert!(vm.reg.v[0x0] == 1);
    Ok(())
}

#[test]
fn fibonacci() -> anyhow::Result<()> {
    let mut vm = VirtualMachine::default();
    // load 0 into V0
    vm.ram[0x200] = 0b0110_0000;
    vm.ram[0x201] = 0b0000_0000;
    // load 1 into v1
    vm.ram[0x202] = 0b0110_0001;
    vm.ram[0x203] = 0b0000_0001;
    // set i to 0xf00
    vm.ram[0x204] = 0b1010_1111;
    vm.ram[0x205] = 0b0000_0000;
    // store v0 in i (start of loop)
    vm.ram[0x206] = 0b1111_0000;
    vm.ram[0x207] = 0b0101_0101;
    // skip next instruction if V2 != 13
    vm.ram[0x208] = 0b0100_0010;
    vm.ram[0x209] = 0b0000_1101;
    // jump to end (0x400)
    vm.ram[0x20a] = 0b0001_0100;
    vm.ram[0x20b] = 0b0000_0000;
    // set V4 = V1
    vm.ram[0x20c] = 0b1000_0100;
    vm.ram[0x20d] = 0b0001_0000;
    // set V1 = V0 + V1
    vm.ram[0x20e] = 0b1000_0001;
    vm.ram[0x20f] = 0b0000_0100;
    // set V0 = V4
    vm.ram[0x210] = 0b1000_0000;
    vm.ram[0x211] = 0b0100_0000;
    // add 1 to V2
    vm.ram[0x212] = 0b0111_0010;
    vm.ram[0x213] = 0b0000_0001;
    // jump to start of loop
    vm.ram[0x214] = 0b0001_0010;
    vm.ram[0x215] = 0b0000_0110;
    // ret to end program
    vm.ram[0x400] = 0b0000_0000;
    vm.ram[0x401] = 0b1110_1110;
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
