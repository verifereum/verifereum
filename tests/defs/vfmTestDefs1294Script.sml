open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1294";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest104.json";
val defs = mapi (define_test "1294") tests;
val () = export_theory_no_docs ();
