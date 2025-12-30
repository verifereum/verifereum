Theory vfmTestDefs2547[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_CALLCODE_ToOneStorageKey_OOGRevert_Paris.json";
val defs = mapi (define_test "2547") tests;
