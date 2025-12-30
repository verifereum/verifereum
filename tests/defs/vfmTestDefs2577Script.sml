Theory vfmTestDefs2577[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_TransactionCALL_ToEmpty_Paris.json";
val defs = mapi (define_test "2577") tests;
