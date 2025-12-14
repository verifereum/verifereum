open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1560";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest352.json";
val defs = mapi (define_test "1560") tests;
val () = export_theory_no_docs ();
