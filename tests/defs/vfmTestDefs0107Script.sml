open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0107";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/test_selfdestruct_created_in_same_tx_with_revert.json";
val defs = mapi (define_test "0107") tests;
val () = export_theory_no_docs ();
