open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2796";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/pairingTest.json";
val defs = mapi (define_test "2796") tests;
val () = export_theory_no_docs ();
