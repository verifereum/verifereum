Theory vfmTestDefs1238[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_TransactionCALL_ToEmpty_Paris.json";
val defs = mapi (define_test "1238") tests;
