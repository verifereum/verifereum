Theory vfmTestDefs1221[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_CALL.json";
val defs = mapi (define_test "1221") tests;
