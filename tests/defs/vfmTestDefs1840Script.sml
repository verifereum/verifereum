open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1840";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest535.json";
val defs = mapi (define_test "1840") tests;
val () = export_theory_no_docs ();
