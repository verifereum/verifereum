open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1556";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest27.json";
val defs = mapi (define_test "1556") tests;
val () = export_theory_no_docs ();
