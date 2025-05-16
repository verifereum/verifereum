open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1336";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest150.json";
val defs = mapi (define_test "1336") tests;
val () = export_theory_no_docs ();
