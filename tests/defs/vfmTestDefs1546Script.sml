open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1546";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest337.json";
val defs = mapi (define_test "1546") tests;
val () = export_theory_no_docs ();
