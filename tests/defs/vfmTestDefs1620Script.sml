open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1620";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest338.json";
val defs = mapi (define_test "1620") tests;
val () = export_theory_no_docs ();
