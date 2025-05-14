open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1476";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest175.json";
val defs = mapi (define_test "1476") tests;
val () = export_theory_no_docs ();
