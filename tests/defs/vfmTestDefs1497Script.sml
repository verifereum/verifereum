open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1497";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest200.json";
val defs = mapi (define_test "1497") tests;
val () = export_theory_no_docs ();
