open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1559";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest5.json";
val defs = mapi (define_test "1559") tests;
val () = export_theory_no_docs ();
