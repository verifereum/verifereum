open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1673";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest45.json";
val defs = mapi (define_test "1673") tests;
val () = export_theory_no_docs ();
