open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1592";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest90.json";
val defs = mapi (define_test "1592") tests;
val () = export_theory_no_docs ();
