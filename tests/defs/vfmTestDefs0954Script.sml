open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0954";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawCallCodeGas.json";
val defs = mapi (define_test "0954") tests;
val () = export_theory_no_docs ();
