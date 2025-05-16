open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1305";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest116.json";
val defs = mapi (define_test "1305") tests;
val () = export_theory_no_docs ();
