Theory vfmTestDefs2550[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_CALL_ToNonZeroBalance_OOGRevert.json";
val defs = mapi (define_test "2550") tests;
