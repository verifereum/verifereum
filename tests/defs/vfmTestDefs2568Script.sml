Theory vfmTestDefs2568[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_DELEGATECALL.json";
val defs = mapi (define_test "2568") tests;
