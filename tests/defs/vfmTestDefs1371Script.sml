open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1371";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest19.json";
val defs = mapi (define_test "1371") tests;
val () = export_theory_no_docs ();
