open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1452";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest280.json";
val defs = mapi (define_test "1452") tests;
val () = export_theory_no_docs ();
