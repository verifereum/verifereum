open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1758";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest576.json";
val defs = mapi (define_test "1758") tests;
val () = export_theory_no_docs ();
