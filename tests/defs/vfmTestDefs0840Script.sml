open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0840";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawCallCodeGasMemoryAsk.json";
val defs = mapi (define_test "0840") tests;
val () = export_theory_no_docs ();
