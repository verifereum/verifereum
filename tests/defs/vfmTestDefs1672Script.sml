open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1672";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest473.json";
val defs = mapi (define_test "1672") tests;
val () = export_theory_no_docs ();
