open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1338";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest153.json";
val defs = mapi (define_test "1338") tests;
val () = export_theory_no_docs ();
