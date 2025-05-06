open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1867";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest569.json";
val defs = mapi (define_test "1867") tests;
val () = export_theory_no_docs ();
