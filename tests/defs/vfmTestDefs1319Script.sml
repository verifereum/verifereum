open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1319";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest131.json";
val defs = mapi (define_test "1319") tests;
val () = export_theory_no_docs ();
