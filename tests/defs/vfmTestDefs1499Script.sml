open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1499";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest287.json";
val defs = mapi (define_test "1499") tests;
val () = export_theory_no_docs ();
