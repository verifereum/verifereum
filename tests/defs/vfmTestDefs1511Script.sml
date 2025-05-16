open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1511";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest343.json";
val defs = mapi (define_test "1511") tests;
val () = export_theory_no_docs ();
