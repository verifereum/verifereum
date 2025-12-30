Theory vfmTestDefs2551[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_CALL_ToOneStorageKey_OOGRevert_Paris.json";
val defs = mapi (define_test "2551") tests;
