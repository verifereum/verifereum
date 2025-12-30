Theory vfmTestDefs2544[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_CALLCODE_OOGRevert.json";
val defs = mapi (define_test "2544") tests;
