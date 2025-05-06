open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1416";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest112.json";
val defs = mapi (define_test "1416") tests;
val () = export_theory_no_docs ();
