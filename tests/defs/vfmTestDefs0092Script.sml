open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0092";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/reentrancy_selfdestruct_revert/reentrancy_selfdestruct_revert.json";
val defs = mapi (define_test "0092") tests;
val () = export_theory_no_docs ();
