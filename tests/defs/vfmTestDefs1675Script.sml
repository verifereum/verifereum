open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1675";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest476.json";
val defs = mapi (define_test "1675") tests;
val () = export_theory_no_docs ();
