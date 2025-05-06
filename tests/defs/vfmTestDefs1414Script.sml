open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1414";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest110.json";
val defs = mapi (define_test "1414") tests;
val () = export_theory_no_docs ();
