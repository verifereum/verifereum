open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1523";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest226.json";
val defs = mapi (define_test "1523") tests;
val () = export_theory_no_docs ();
