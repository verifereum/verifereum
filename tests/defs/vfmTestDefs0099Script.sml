open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0099";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/selfdestruct/self_destructing_initcode_create_tx.json";
val defs = mapi (define_test "0099") tests;
val () = export_theory_no_docs ();
