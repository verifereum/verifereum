open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0970";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawCreateGasValueTransfer.json";
val defs = mapi (define_test "0970") tests;
val () = export_theory_no_docs ();
