open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1694";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest77.json";
val defs = mapi (define_test "1694") tests;
val () = export_theory_no_docs ();
