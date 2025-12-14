open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0947";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawExtCodeSizeGas.json";
val defs = mapi (define_test "0947") tests;
val () = export_theory_no_docs ();
