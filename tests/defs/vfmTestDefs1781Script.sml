open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1781";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest467.json";
val defs = mapi (define_test "1781") tests;
val () = export_theory_no_docs ();
