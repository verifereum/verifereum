Theory vfmTestDefs2565[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_CALL_ToEmpty_Paris.json";
val defs = mapi (define_test "2565") tests;
