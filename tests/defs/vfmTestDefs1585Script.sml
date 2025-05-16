open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1585";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest83.json";
val defs = mapi (define_test "1585") tests;
val () = export_theory_no_docs ();
