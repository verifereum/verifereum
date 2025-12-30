Theory vfmTestDefs1886[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/call_then_create_successful_then_returndatasize.json";
val defs = mapi (define_test "1886") tests;
