open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1393";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest211.json";
val defs = mapi (define_test "1393") tests;
val () = export_theory_no_docs ();
