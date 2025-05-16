open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1487";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest313.json";
val defs = mapi (define_test "1487") tests;
val () = export_theory_no_docs ();
