open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1394";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest212.json";
val defs = mapi (define_test "1394") tests;
val () = export_theory_no_docs ();
