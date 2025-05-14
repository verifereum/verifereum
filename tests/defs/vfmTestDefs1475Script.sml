open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1475";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest174.json";
val defs = mapi (define_test "1475") tests;
val () = export_theory_no_docs ();
