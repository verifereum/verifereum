open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1503";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest202.json";
val defs = mapi (define_test "1503") tests;
val () = export_theory_no_docs ();
