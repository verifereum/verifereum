open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1531";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest242.json";
val defs = mapi (define_test "1531") tests;
val () = export_theory_no_docs ();
