open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1569";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest60.json";
val defs = mapi (define_test "1569") tests;
val () = export_theory_no_docs ();
