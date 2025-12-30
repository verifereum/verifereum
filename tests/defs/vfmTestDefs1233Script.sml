Theory vfmTestDefs1233[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_SUICIDE.json";
val defs = mapi (define_test "1233") tests;
