open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1624";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest81.json";
val defs = mapi (define_test "1624") tests;
val () = export_theory_no_docs ();
