open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1685";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest440.json";
val defs = mapi (define_test "1685") tests;
val () = export_theory_no_docs ();
