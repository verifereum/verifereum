open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1323";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest137.json";
val defs = mapi (define_test "1323") tests;
val () = export_theory_no_docs ();
