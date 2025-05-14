open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1593";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest302.json";
val defs = mapi (define_test "1593") tests;
val () = export_theory_no_docs ();
