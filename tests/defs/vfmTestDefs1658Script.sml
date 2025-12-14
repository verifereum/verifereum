open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1658";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest408.json";
val defs = mapi (define_test "1658") tests;
val () = export_theory_no_docs ();
