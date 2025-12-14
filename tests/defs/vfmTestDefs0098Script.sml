open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0098";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_create_selfdestruct_same_tx.json";
val defs = mapi (define_test "0098") tests;
val () = export_theory_no_docs ();
