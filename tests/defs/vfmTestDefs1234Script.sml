Theory vfmTestDefs1234[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_SUICIDE_ToEmpty_Paris.json";
val defs = mapi (define_test "1234") tests;
