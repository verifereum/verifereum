open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1533";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest321.json";
val defs = mapi (define_test "1533") tests;
val () = export_theory_no_docs ();
