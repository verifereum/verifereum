Theory vfmTestDefs2561[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_CALLCODE.json";
val defs = mapi (define_test "2561") tests;
