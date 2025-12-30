Theory vfmTestDefs2553[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_DELEGATECALL_ToEmpty_OOGRevert_Paris.json";
val defs = mapi (define_test "2553") tests;
