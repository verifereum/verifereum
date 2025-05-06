open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0982";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/gasCost.json";
val defs = mapi (define_test "0982") tests;
val () = export_theory_no_docs ();
