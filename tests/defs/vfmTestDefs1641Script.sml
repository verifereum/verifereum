open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1641";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest36.json";
val defs = mapi (define_test "1641") tests;
val () = export_theory_no_docs ();
