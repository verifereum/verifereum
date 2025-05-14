open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1562";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest271.json";
val defs = mapi (define_test "1562") tests;
val () = export_theory_no_docs ();
