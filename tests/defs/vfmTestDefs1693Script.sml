open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1693";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest69.json";
val defs = mapi (define_test "1693") tests;
val () = export_theory_no_docs ();
