open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1461";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest158.json";
val defs = mapi (define_test "1461") tests;
val () = export_theory_no_docs ();
