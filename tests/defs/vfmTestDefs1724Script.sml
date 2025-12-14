open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1724";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest485.json";
val defs = mapi (define_test "1724") tests;
val () = export_theory_no_docs ();
