open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1513";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest346.json";
val defs = mapi (define_test "1513") tests;
val () = export_theory_no_docs ();
