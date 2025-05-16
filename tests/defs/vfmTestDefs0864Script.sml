open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0864";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawExtCodeCopyMemoryGas.json";
val defs = mapi (define_test "0864") tests;
val () = export_theory_no_docs ();
