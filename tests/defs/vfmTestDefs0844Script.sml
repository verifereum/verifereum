open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0844";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawCallCodeGasValueTransferMemoryAsk.json";
val defs = mapi (define_test "0844") tests;
val () = export_theory_no_docs ();
