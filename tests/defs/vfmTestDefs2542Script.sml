open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2542";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_TransactionCALL_ToEmpty_Paris.json";
val defs = mapi (define_test "2542") tests;
val () = export_theory_no_docs ();
