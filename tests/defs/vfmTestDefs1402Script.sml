open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1402";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest178.json";
val defs = mapi (define_test "1402") tests;
val () = export_theory_no_docs ();
