Theory vfmTestDefs1229[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stNonZeroCallsTest/NonZeroValue_DELEGATECALL.json";
val defs = mapi (define_test "1229") tests;
