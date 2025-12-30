Theory vfmTestDefs2563[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_CALLCODE_ToNonZeroBalance.json";
val defs = mapi (define_test "2563") tests;
