open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1595";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest308.json";
val defs = mapi (define_test "1595") tests;
val () = export_theory_no_docs ();
