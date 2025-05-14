open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1525";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest228.json";
val defs = mapi (define_test "1525") tests;
val () = export_theory_no_docs ();
