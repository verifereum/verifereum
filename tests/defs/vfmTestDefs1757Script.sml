open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1757";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest575.json";
val defs = mapi (define_test "1757") tests;
val () = export_theory_no_docs ();
