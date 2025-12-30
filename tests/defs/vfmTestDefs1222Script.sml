Theory vfmTestDefs1222[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_CALLCODE.json";
val defs = mapi (define_test "1222") tests;
