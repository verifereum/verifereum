open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1438";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest266.json";
val defs = mapi (define_test "1438") tests;
val () = export_theory_no_docs ();
