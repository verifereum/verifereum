open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1542";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest376.json";
val defs = mapi (define_test "1542") tests;
val () = export_theory_no_docs ();
