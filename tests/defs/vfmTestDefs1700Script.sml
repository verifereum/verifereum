open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1700";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest80.json";
val defs = mapi (define_test "1700") tests;
val () = export_theory_no_docs ();
