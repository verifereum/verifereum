Theory vfmTestDefs1224[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_CALLCODE_ToNonNonZeroBalance.json";
val defs = mapi (define_test "1224") tests;
