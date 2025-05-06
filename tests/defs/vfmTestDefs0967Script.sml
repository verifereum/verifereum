open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0967";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawCreateFailGasValueTransfer2.json";
val defs = mapi (define_test "0967") tests;
val () = export_theory_no_docs ();
