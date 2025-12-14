open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1428";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest205.json";
val defs = mapi (define_test "1428") tests;
val () = export_theory_no_docs ();
