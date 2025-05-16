open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1313";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest124.json";
val defs = mapi (define_test "1313") tests;
val () = export_theory_no_docs ();
