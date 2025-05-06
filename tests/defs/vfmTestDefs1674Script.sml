open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1674";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest51.json";
val defs = mapi (define_test "1674") tests;
val () = export_theory_no_docs ();
