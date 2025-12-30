Theory vfmTestDefs1226[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_CALL_ToEmpty_Paris.json";
val defs = mapi (define_test "1226") tests;
