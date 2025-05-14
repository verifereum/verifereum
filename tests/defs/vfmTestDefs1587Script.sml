open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1587";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest298.json";
val defs = mapi (define_test "1587") tests;
val () = export_theory_no_docs ();
