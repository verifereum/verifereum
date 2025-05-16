open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1376";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest195.json";
val defs = mapi (define_test "1376") tests;
val () = export_theory_no_docs ();
