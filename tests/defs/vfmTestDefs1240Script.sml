Theory vfmTestDefs1240[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_TransactionCALL_ToOneStorageKey_Paris.json";
val defs = mapi (define_test "1240") tests;
