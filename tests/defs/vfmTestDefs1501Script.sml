open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1501";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest29.json";
val defs = mapi (define_test "1501") tests;
val () = export_theory_no_docs ();
