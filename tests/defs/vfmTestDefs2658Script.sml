open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2658";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_TransactionCALL_ToOneStorageKey_Paris.json";
val defs = mapi (define_test "2658") tests;
val () = export_theory_no_docs ();
