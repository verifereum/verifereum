open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2461";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransitionTest/createNameRegistratorPerTxsAfter.json";
val defs = mapi (define_test "2461") tests;
val () = export_theory_no_docs ();
