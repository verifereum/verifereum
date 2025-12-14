open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0108";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_selfdestruct_created_same_block_different_tx.json";
val defs = mapi (define_test "0108") tests;
val () = export_theory_no_docs ();
