open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1801";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest633.json";
val defs = mapi (define_test "1801") tests;
val () = export_theory_no_docs ();
