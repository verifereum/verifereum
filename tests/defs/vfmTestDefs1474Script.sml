open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1474";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest301.json";
val defs = mapi (define_test "1474") tests;
val () = export_theory_no_docs ();
