open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1589";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest88.json";
val defs = mapi (define_test "1589") tests;
val () = export_theory_no_docs ();
