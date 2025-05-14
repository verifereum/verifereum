open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1648";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest362.json";
val defs = mapi (define_test "1648") tests;
val () = export_theory_no_docs ();
