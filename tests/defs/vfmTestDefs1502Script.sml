open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1502";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest334.json";
val defs = mapi (define_test "1502") tests;
val () = export_theory_no_docs ();
