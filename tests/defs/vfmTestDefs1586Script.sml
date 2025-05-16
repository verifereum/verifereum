open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1586";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest84.json";
val defs = mapi (define_test "1586") tests;
val () = export_theory_no_docs ();
