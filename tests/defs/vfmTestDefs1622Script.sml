open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1622";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest78.json";
val defs = mapi (define_test "1622") tests;
val () = export_theory_no_docs ();
