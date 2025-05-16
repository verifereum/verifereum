open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1567";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest59.json";
val defs = mapi (define_test "1567") tests;
val () = export_theory_no_docs ();
