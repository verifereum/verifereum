open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1406";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest227.json";
val defs = mapi (define_test "1406") tests;
val () = export_theory_no_docs ();
