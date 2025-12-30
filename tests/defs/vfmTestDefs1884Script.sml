Theory vfmTestDefs1884[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/call_outsize_then_create_successful_then_returndatasize.json";
val defs = mapi (define_test "1884") tests;
