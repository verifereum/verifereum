Theory vfmTestDefs0814[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/call_then_create2_successful_then_returndatasize.json";
val defs = mapi (define_test "0814") tests;
