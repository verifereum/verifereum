open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1316";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest129.json";
val defs = mapi (define_test "1316") tests;
val () = export_theory_no_docs ();
