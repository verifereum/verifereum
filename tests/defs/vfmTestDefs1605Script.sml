open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1605";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest55.json";
val defs = mapi (define_test "1605") tests;
val () = export_theory_no_docs ();
