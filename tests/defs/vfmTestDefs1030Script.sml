open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1030";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemExpandingEIP150Calls/NewGasPriceForCodesWithMemExpandingCalls.json";
val defs = mapi (define_test "1030") tests;
val () = export_theory_no_docs ();
