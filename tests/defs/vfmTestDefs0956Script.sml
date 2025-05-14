open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0956";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawCallCodeGasMemory.json";
val defs = mapi (define_test "0956") tests;
val () = export_theory_no_docs ();
