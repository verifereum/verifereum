open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1796";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest484.json";
val defs = mapi (define_test "1796") tests;
val () = export_theory_no_docs ();
