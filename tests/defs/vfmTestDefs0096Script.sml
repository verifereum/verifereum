open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0096";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip6780_selfdestruct/selfdestruct/create_selfdestruct_same_tx_increased_nonce.json";
val defs = mapi (define_test "0096") tests;
val () = export_theory_no_docs ();
