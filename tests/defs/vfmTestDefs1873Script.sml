open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1873";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest577.json";
val defs = mapi (define_test "1873") tests;
val () = export_theory_no_docs ();
