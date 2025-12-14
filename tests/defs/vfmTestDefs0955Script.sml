open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0955";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/gasCostMemSeg.json";
val defs = mapi (define_test "0955") tests;
val () = export_theory_no_docs ();
