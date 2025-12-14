open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1374";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest148.json";
val defs = mapi (define_test "1374") tests;
val () = export_theory_no_docs ();
