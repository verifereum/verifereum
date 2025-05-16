open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1384";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest201.json";
val defs = mapi (define_test "1384") tests;
val () = export_theory_no_docs ();
