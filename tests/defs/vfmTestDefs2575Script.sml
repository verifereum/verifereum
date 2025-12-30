Theory vfmTestDefs2575[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_SUICIDE_ToOneStorageKey_Paris.json";
val defs = mapi (define_test "2575") tests;
