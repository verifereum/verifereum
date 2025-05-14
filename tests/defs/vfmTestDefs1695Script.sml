open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1695";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest73.json";
val defs = mapi (define_test "1695") tests;
val () = export_theory_no_docs ();
