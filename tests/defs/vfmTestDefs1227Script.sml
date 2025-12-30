Theory vfmTestDefs1227[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_CALL_ToNonNonZeroBalance.json";
val defs = mapi (define_test "1227") tests;
