open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0801";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stChainId/chainIdGasCost.json";
val defs = mapi (define_test "0801") tests;
val () = export_theory_no_docs ();
