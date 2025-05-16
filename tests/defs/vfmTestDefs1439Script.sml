open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1439";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest267.json";
val defs = mapi (define_test "1439") tests;
val () = export_theory_no_docs ();
