Theory vfmTestDefs1235[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_SUICIDE_ToNonNonZeroBalance.json";
val defs = mapi (define_test "1235") tests;
