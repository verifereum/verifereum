open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1684";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest487.json";
val defs = mapi (define_test "1684") tests;
val () = export_theory_no_docs ();
