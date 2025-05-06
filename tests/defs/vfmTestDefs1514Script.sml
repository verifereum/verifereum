open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1514";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest22.json";
val defs = mapi (define_test "1514") tests;
val () = export_theory_no_docs ();
