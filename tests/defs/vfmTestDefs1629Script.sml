open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1629";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest420.json";
val defs = mapi (define_test "1629") tests;
val () = export_theory_no_docs ();
