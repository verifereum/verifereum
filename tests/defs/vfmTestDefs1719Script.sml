open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1719";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest393.json";
val defs = mapi (define_test "1719") tests;
val () = export_theory_no_docs ();
