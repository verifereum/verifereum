open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1750";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest565.json";
val defs = mapi (define_test "1750") tests;
val () = export_theory_no_docs ();
