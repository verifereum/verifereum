open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1614";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest326.json";
val defs = mapi (define_test "1614") tests;
val () = export_theory_no_docs ();
