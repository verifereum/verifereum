open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1662";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest383.json";
val defs = mapi (define_test "1662") tests;
val () = export_theory_no_docs ();
