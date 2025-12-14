open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1417";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest195.json";
val defs = mapi (define_test "1417") tests;
val () = export_theory_no_docs ();
