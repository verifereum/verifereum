open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1574";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest67.json";
val defs = mapi (define_test "1574") tests;
val () = export_theory_no_docs ();
