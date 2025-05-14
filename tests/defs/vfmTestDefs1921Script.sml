open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1921";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest636.json";
val defs = mapi (define_test "1921") tests;
val () = export_theory_no_docs ();
