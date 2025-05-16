open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1333";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest148.json";
val defs = mapi (define_test "1333") tests;
val () = export_theory_no_docs ();
