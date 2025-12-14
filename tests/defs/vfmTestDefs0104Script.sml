open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0104";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_reentrancy_selfdestruct_revert.json";
val defs = mapi (define_test "0104") tests;
val () = export_theory_no_docs ();
