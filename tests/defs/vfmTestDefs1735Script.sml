open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1735";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest408.json";
val defs = mapi (define_test "1735") tests;
val () = export_theory_no_docs ();
