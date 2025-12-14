open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1558";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest350.json";
val defs = mapi (define_test "1558") tests;
val () = export_theory_no_docs ();
