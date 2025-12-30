Theory vfmTestDefs1236[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_SUICIDE_ToOneStorageKey_Paris.json";
val defs = mapi (define_test "1236") tests;
