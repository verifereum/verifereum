open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0866";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/eip2929-ff.json";
val defs = mapi (define_test "0866") tests;
val () = export_theory_no_docs ();
