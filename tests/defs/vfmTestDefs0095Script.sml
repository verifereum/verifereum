open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0095";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/selfdestruct/create_selfdestruct_same_tx.json";
val defs = mapi (define_test "0095") tests;
val () = export_theory_no_docs ();
