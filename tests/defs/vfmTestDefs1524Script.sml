open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1524";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest357.json";
val defs = mapi (define_test "1524") tests;
val () = export_theory_no_docs ();
